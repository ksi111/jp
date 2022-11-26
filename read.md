// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title CollateralLocker holds custody of collateralAsset for Loans.
contract CollateralLocker {

    using SafeERC20 for IERC20;

    IERC20  public immutable collateralAsset;  // Address the loan is funded with
    address public immutable loan;             // Loan contract address this CollateralLocker is attached to

    constructor(address _collateralAsset, address _loan) public {
        collateralAsset = IERC20(_collateralAsset);
        loan            = _loan;
    }

    modifier isLoan() {
        require(msg.sender == loan, "CollateralLocker:MSG_SENDER_NOT_LOAN");
        _;
    }

    /**
        @dev Transfers amt of collateralAsset to dst. Only Loan can call this function.
        @param dst Desintation to transfer collateralAsset to
        @param amt Amount of collateralAsset to transfer
    */
    function pull(address dst, uint256 amt) isLoan external {
        collateralAsset.safeTransfer(dst, amt);
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./CollateralLocker.sol";

import "./interfaces/ILoanFactory.sol";

/// @title CollateralLockerFactory instantiates CollateralLockers.
contract CollateralLockerFactory {

    mapping(address => address) public owner;     // Mapping of locker contract address to its owner i.e owner[locker] = Owner of the collateral locker
    mapping(address => bool)    public isLocker;  // True if collateral locker was created by this factory, otherwise false

    uint8 public constant factoryType = 0;  // i.e FactoryType::COLLATERAL_LOCKER_FACTORY

    /**
        @dev Instantiate a CollateralLocker contract.
        @param collateralAsset The asset this collateral locker will escrow
        @return Address of the instantiated collateral locker
    */
    function newLocker(address collateralAsset) external returns (address) {
        address collateralLocker   = address(new CollateralLocker(collateralAsset, msg.sender));
        owner[collateralLocker]    = msg.sender;
        isLocker[collateralLocker] = true;
        return collateralLocker;
    }
}




// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ILoan.sol";

import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";
import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title DebtLocker holds custody of LoanFDT tokens.
contract DebtLocker {

    using SafeMath  for uint256;
    using SafeERC20 for IERC20;

    uint256 constant WAD = 10 ** 18;

    ILoan   public immutable loan;            // The Loan contract this locker is holding tokens for
    IERC20  public immutable liquidityAsset;  // The liquidityAsset this locker can claim
    address public immutable pool;            // The owner of this Locker (the Pool)

    uint256 public lastPrincipalPaid;    // Loan total principal   paid at last time claim() was called
    uint256 public lastInterestPaid;     // Loan total interest    paid at last time claim() was called
    uint256 public lastFeePaid;          // Loan total fees        paid at last time claim() was called
    uint256 public lastExcessReturned;   // Loan total excess  returned at last time claim() was called
    uint256 public lastDefaultSuffered;  // Loan total default suffered at last time claim() was called
    uint256 public lastAmountRecovered;  // Liquidity asset (a.k.a. loan asset) recovered from liquidation of Loan collateral

    modifier isPool() {
        require(msg.sender == pool, "DebtLocker:MSG_SENDER_NOT_POOL");
        _;
    }

    constructor(address _loan, address _pool) public {
        loan           = ILoan(_loan);
        pool           = _pool;
        liquidityAsset = IERC20(ILoan(_loan).liquidityAsset());
    }

    // Note: If newAmt > 0, totalNewAmt will always be greater than zero.
    function calcAllotment(uint256 newAmt, uint256 totalClaim, uint256 totalNewAmt) internal pure returns (uint256) {
        return newAmt == uint256(0) ? uint256(0) : newAmt.mul(totalClaim).div(totalNewAmt);
    }

    /**
        @dev    Claim funds distribution for Loan via FDT.
        @return [0] = Total Claimed
                [1] = Interest Claimed
                [2] = Principal Claimed
                [3] = Pool Delegate Fee Claimed
                [4] = Excess Returned Claimed
                [5] = Amount Recovered (from Liquidation)
                [6] = Default Suffered
    */
    function claim() external isPool returns(uint256[7] memory) {

        // Initialize newDefaultSuffered as zero
        uint256 newDefaultSuffered   = uint256(0);
        uint256 loan_defaultSuffered = loan.defaultSuffered();

        // If a default has occurred, update storage variable and update memory variable from zero for return.
        // `newDefaultSuffered` represents the proportional loss that the DebtLocker registers based on its balance
        // of LoanFDTs in comparison to the totalSupply of LoanFDTs.
        // Default will occur only once so below statement will only be `true` once.
        if (lastDefaultSuffered == uint256(0) && loan_defaultSuffered > uint256(0)) {
            newDefaultSuffered = lastDefaultSuffered = calcAllotment(loan.balanceOf(address(this)), loan_defaultSuffered, loan.totalSupply());
        }

        // Account for any transfers into Loan that have occurred since last call
        loan.updateFundsReceived();

        // If there are claimable funds, calculate portions and claim using LoanFDT
        if (loan.withdrawableFundsOf(address(this)) > uint256(0)) {

            // Calculate payment deltas
            uint256 newInterest  = loan.interestPaid() - lastInterestPaid;    // `loan.interestPaid`  updated in `loan._makePayment()`
            uint256 newPrincipal = loan.principalPaid() - lastPrincipalPaid;  // `loan.principalPaid` updated in `loan._makePayment()`

            // Update storage variables for next delta calculation
            lastInterestPaid  = loan.interestPaid();
            lastPrincipalPaid = loan.principalPaid();

            // Calculate one-time deltas if storage variables have not yet been updated
            uint256 newFee             = lastFeePaid         == uint256(0) ? loan.feePaid()         : uint256(0);  // `loan.feePaid`          updated in `loan.drawdown()`
            uint256 newExcess          = lastExcessReturned  == uint256(0) ? loan.excessReturned()  : uint256(0);  // `loan.excessReturned`   updated in `loan.unwind()` OR `loan.drawdown()` if `amt < fundingLockerBal`
            uint256 newAmountRecovered = lastAmountRecovered == uint256(0) ? loan.amountRecovered() : uint256(0);  // `loan.amountRecovered`  updated in `loan.triggerDefault()`

            // Update DebtLocker storage variable if Loan storage variable has been updated since last claim
            if (newFee > 0)             lastFeePaid         = newFee;
            if (newExcess > 0)          lastExcessReturned  = newExcess;
            if (newAmountRecovered > 0) lastAmountRecovered = newAmountRecovered;

            // Withdraw all claimable funds via LoanFDT
            uint256 beforeBal = liquidityAsset.balanceOf(address(this));                 // Current balance of DebtLocker (accounts for direct inflows)
            loan.withdrawFunds();                                                        // Transfer funds from Loan to DebtLocker
            uint256 claimBal  = liquidityAsset.balanceOf(address(this)).sub(beforeBal);  // Amount claimed from Loan using LoanFDT

            // Calculate sum of all deltas, to be used to calculate portions for metadata
            uint256 sum = newInterest.add(newPrincipal).add(newFee).add(newExcess).add(newAmountRecovered);

            // Calculate payment portions based on LoanFDT claim
            newInterest  = calcAllotment(newInterest,  claimBal, sum);
            newPrincipal = calcAllotment(newPrincipal, claimBal, sum);

            // Calculate one-time portions based on LoanFDT claim
            newFee             = calcAllotment(newFee,             claimBal, sum);
            newExcess          = calcAllotment(newExcess,          claimBal, sum);
            newAmountRecovered = calcAllotment(newAmountRecovered, claimBal, sum);

            liquidityAsset.safeTransfer(pool, claimBal);  // Transfer entire amount claimed using LoanFDT

            // Return claim amount plus all relevant metadata, to be used by Pool for further claim logic
            // Note: newInterest + newPrincipal + newFee + newExcess + newAmountRecovered = claimBal - dust
            //       The dust on the right side of the equation gethers in the pool after transfers are made
            return([claimBal, newInterest, newPrincipal, newFee, newExcess, newAmountRecovered, newDefaultSuffered]);
        }

        // Handles case where no claimable funds are present but a default must be registered (zero-collateralized loans defaulting)
        return([0, 0, 0, 0, 0, 0, newDefaultSuffered]);
    }

    /**
        @dev Liquidate a loan that is held by this contract. Only called by the pool contract.
    */
    function triggerDefault() external isPool {
        loan.triggerDefault();
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./DebtLocker.sol";

/// @title DebtLockerFactory instantiates DebtLockers.
contract DebtLockerFactory {

    mapping(address => address) public owner;     // Mapping of locker contract address to its owner i.e owner[locker] = Owner of the debt locker
    mapping(address => bool)    public isLocker;  // True if debt locker was created in this factory, otherwise false

    uint8 public constant factoryType = 1;  // i.e LockerFactoryTypes::DEBT_LOCKER_FACTORY

    /**
        @dev Instantiate a DebtLocker contract.
        @param  loan The loan this debt locker will escrow tokens for
        @return Address of the instantiated debt locker
    */
    function newLocker(address loan) external returns (address) {
        address debtLocker   = address(new DebtLocker(loan, msg.sender));
        owner[debtLocker]    = msg.sender;
        isLocker[debtLocker] = true;
        return debtLocker;
    }
}




// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title FundingLocker holds custody of liquidityAsset tokens during the funding period of a Loan.
contract FundingLocker {

    using SafeERC20 for IERC20;

    IERC20  public immutable liquidityAsset;  // Asset the Loan was funded with
    address public immutable loan;            // Loan this FundingLocker has funded

    constructor(address _liquidityAsset, address _loan) public {
        liquidityAsset = IERC20(_liquidityAsset);
        loan           = _loan;
    }

    modifier isLoan() {
        require(msg.sender == loan, "FundingLocker:MSG_SENDER_NOT_LOAN");
        _;
    }

    /**
        @dev Transfers amt of liquidityAsset to dst. Only the Loan can call this function.
        @param dst Desintation to transfer liquidityAsset to
        @param amt Amount of liquidityAsset to transfer
    */
    function pull(address dst, uint256 amt) isLoan external {
        liquidityAsset.safeTransfer(dst, amt);
    }

    /**
        @dev Transfers entire amount of liquidityAsset held in escrow to Loan. Only the Loan can call this function.
    */
    function drain() isLoan external {
        uint256 amt = liquidityAsset.balanceOf(address(this));
        liquidityAsset.safeTransfer(loan, amt);
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./FundingLocker.sol";

import "./interfaces/ILoanFactory.sol";

/// @title FundingLockerFactory instantiates FundingLockers.
contract FundingLockerFactory {

    mapping(address => address) public owner;     // Mapping of locker contract address to its owner i.e owner[locker] = Owner of the funding locker
    mapping(address => bool)    public isLocker;  // True if funding locker was created by this factory, otherwise false

    uint8 public constant factoryType = 2;  // i.e FactoryType::FUNDING_LOCKER_FACTORY

    /**
        @dev Instantiate a FundingLocker contract.
        @param liquidityAsset The asset this funding locker will escrow
        @return Address of the instantiated funding locker
    */
    function newLocker(address liquidityAsset) public returns (address) {
        address fundingLocker   = address(new FundingLocker(liquidityAsset, msg.sender));
        owner[fundingLocker]    = msg.sender;
        isLocker[fundingLocker] = true;
        return fundingLocker;
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ILoan.sol";
import "./interfaces/IRepaymentCalc.sol";

import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";

/// @title LateFeeCalc calculates late fees on Loans.
contract LateFeeCalc {

    using SafeMath for uint256;

    uint8   public constant calcType = 11;  // "LATEFEE type"
    bytes32 public constant name     = 'FLAT';

    uint256 public immutable lateFee;  // The fee in basis points, charged on the payment amount.

    constructor(uint256 _lateFee) public {
        lateFee = _lateFee;
    }

    /**
        @dev    Calculates the late fee payment for a loan.
        @param  interest Amount of interest to be used to calculate late fee for
        @return Late fee that is charged to borrower
    */
    function getLateFee(uint256 interest) view public returns(uint256) {
        return interest.mul(lateFee).div(10_000);
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ILoan.sol";

import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title LiquidityLocker holds custody of liquidityAsset tokens for a given Pool.
contract LiquidityLocker {

    using SafeERC20 for IERC20;

    address public immutable pool;            // The Pool that owns this LiquidityLocker, for authorization purposes
    IERC20  public immutable liquidityAsset;  // The asset which this LiquidityLocker will escrow

    constructor(address _liquidityAsset, address _pool) public {
        liquidityAsset = IERC20(_liquidityAsset);
        pool           = _pool;
    }

    modifier isPool() {
        require(msg.sender == pool, "LiquidityLocker:MSG_SENDER_NOT_POOL");
        _;
    }

    /**
        @dev Transfers amt of liquidityAsset to dst. Only the Pool can call this function.
        @param dst Desintation to transfer liquidityAsset to
        @param amt Amount of liquidityAsset to transfer
    */
    function transfer(address dst, uint256 amt) external isPool {
        require(dst != address(0), "LiquidityLocker:NULL_TRASNFER_DST");
        liquidityAsset.safeTransfer(dst, amt);
    }

    /**
        @dev Fund a loan using available assets in this liquidity locker. Only the Pool can call this function.
        @param  loan       The loan to fund
        @param  debtLocker The locker that will escrow debt tokens
        @param  amt        Amount of liquidityAsset to fund the loan for
    */
    function fundLoan(address loan, address debtLocker, uint256 amt) external isPool {
        liquidityAsset.safeApprove(loan, amt);
        ILoan(loan).fundLoan(debtLocker, amt);
    }
}






// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./LiquidityLocker.sol";

/// @title LiquidityLockerFactory instantiates LiquidityLockers.
contract LiquidityLockerFactory {

    mapping(address => address) public owner;     // Mapping of locker contract address to its owner i.e owner[locker] = Owner of the liquidity locker
    mapping(address => bool)    public isLocker;  // True if liquidity locker was created by this factory, otherwise false

    uint8 public constant factoryType = 3;        // i.e LockerFactoryTypes::LIQUIDITY_LOCKER_FACTORY

    /**
        @dev Instantiate a LiquidityLocker contract.
        @param  liquidityAsset The asset this liquidity locker will escrow
        @return Address of the instantiated liquidity locker
    */
    function newLocker(address liquidityAsset) external returns (address) {
        address liquidityLocker   = address(new LiquidityLocker(liquidityAsset, msg.sender));
        owner[liquidityLocker]    = msg.sender;
        isLocker[liquidityLocker] = true;
        return liquidityLocker;
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ICollateralLocker.sol";
import "./interfaces/ICollateralLockerFactory.sol";
import "./interfaces/IERC20Details.sol";
import "./interfaces/IFundingLocker.sol";
import "./interfaces/IFundingLockerFactory.sol";
import "./interfaces/IGlobals.sol";
import "./interfaces/ILateFeeCalc.sol";
import "./interfaces/ILiquidityLocker.sol";
import "./interfaces/ILoanFactory.sol";
import "./interfaces/IPool.sol";
import "./interfaces/IPoolFactory.sol";
import "./interfaces/IPremiumCalc.sol";
import "./interfaces/IRepaymentCalc.sol";
import "./interfaces/IUniswapRouter.sol";
import "./library/Util.sol";
import "./library/LoanLib.sol";

import "./token/FDT.sol";

import "lib/openzeppelin-contracts/contracts/utils/Pausable.sol";
import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title Loan maintains all accounting and functionality related to Loans.
contract Loan is FDT, Pausable {

    using SafeMathInt     for int256;
    using SignedSafeMath  for int256;
    using SafeMath        for uint256;
    using SafeERC20       for IERC20;

    /**
        Ready      = The loan has been initialized and is ready for funding (assuming funding period hasn't ended)
        Active     = The loan has been drawdown and the borrower is making payments
        Matured    = The loan is fully paid off and has "matured"
        Expired    = The loan did not initiate, and all funding was returned to lenders
        Liquidated = The loan has been liquidated
    */
    enum State { Ready, Active, Matured, Expired, Liquidated }

    State public loanState;  // The current state of this loan, as defined in the State enum below

    IERC20 public immutable liquidityAsset;     // Asset deposited by lenders into the FundingLocker, when funding this loan
    IERC20 public immutable collateralAsset;    // Asset deposited by borrower into the CollateralLocker, for collateralizing this loan

    address public immutable fundingLocker;     // Funding locker - holds custody of loan funds before drawdown
    address public immutable flFactory;         // Funding locker factory
    address public immutable collateralLocker;  // Collateral locker - holds custody of loan collateral
    address public immutable clFactory;         // Collateral locker factory
    address public immutable borrower;          // Borrower of this loan, responsible for repayments
    address public immutable repaymentCalc;     // The repayment calculator for this loan
    address public immutable lateFeeCalc;       // The late fee calculator for this loan
    address public immutable premiumCalc;       // The premium calculator for this loan
    address public immutable superFactory;      // The factory that deployed this Loan

    mapping(address => bool) public admins;  // Admin addresses that have permission to do certain operations in case of disaster mgt

    uint256 public nextPaymentDue;  // The unix timestamp due date of next payment

    // Loan specifications
    uint256 public immutable apr;                     // APR in basis points
    uint256 public           paymentsRemaining;       // Number of payments remaining on the Loan
    uint256 public immutable termDays;                // Total length of the Loan term in days
    uint256 public immutable paymentIntervalSeconds;  // Time between Loan payments in seconds
    uint256 public immutable requestAmount;           // Total requested amount for Loan
    uint256 public immutable collateralRatio;         // Percentage of value of drawdown amount to post as collateral in basis points
    uint256 public immutable createdAt;               // Timestamp of when Loan was instantiated
    uint256 public immutable fundingPeriod;           // Time for a Loan to be funded in seconds
    uint256 public immutable defaultGracePeriod;      // Time a borrower has after a payment is due to make apayment before a liquidation can occur

    // Accounting variables
    uint256 public principalOwed;   // The principal owed (initially the drawdown amount)
    uint256 public principalPaid;   // Amount of principal  that has been paid by borrower since Loan instantiation
    uint256 public interestPaid;    // Amount of interest   that has been paid by borrower since Loan instantiation
    uint256 public feePaid;         // Amount of fees      that have been paid by borrower since Loan instantiation
    uint256 public excessReturned;  // Amount of excess that has been returned to lenders after Loan drawdown

    // Liquidation variables
    uint256 public amountLiquidated;   // Amount of collateral that has been liquidated after default
    uint256 public amountRecovered;    // Amount of liquidityAsset  that has been recovered  after default
    uint256 public defaultSuffered;    // Difference between `amountRecovered` and `principalOwed` after liquidation
    uint256 public liquidationExcess;  // If `amountRecovered > principalOwed`, amount of liquidityAsset that is to be returned to borrower

    event LoanFunded(uint256 amtFunded, address indexed _fundedBy);
    event BalanceUpdated(address who, address token, uint256 balance);
    event Drawdown(uint256 drawdownAmt);
    event LoanStateChanged(State state);
    event PaymentMade(
        uint totalPaid,
        uint principalPaid,
        uint interestPaid,
        uint paymentsRemaining,
        uint principalOwed,
        uint nextPaymentDue,
        bool latePayment
    );
    event Liquidation(
        uint collateralSwapped,
        uint liquidityAssetReturned,
        uint liquidationExcess,
        uint defaultSuffered
    );

    /**
        @dev Constructor for a Loan.
        @param  _borrower        Will receive the funding when calling `drawdown()`, is also responsible for repayments
        @param  _liquidityAsset  The asset, `borrower` is requesting funding in
        @param  _collateralAsset The asset provided as collateral by `borrower`
        @param  _flFactory       Factory to instantiate FundingLocker with
        @param  _clFactory       Factory to instantiate CollateralLocker with
        @param  specs            Contains specifications for this loan
                specs[0] = apr
                specs[1] = termDays
                specs[2] = paymentIntervalDays (aka PID)
                specs[3] = requestAmount
                specs[4] = collateralRatio
        @param  calcs The calculators used for the loan
                calcs[0] = repaymentCalc
                calcs[1] = lateFeeCalc
                calcs[2] = premiumCalc
    */
    constructor(
        address _borrower,
        address _liquidityAsset,
        address _collateralAsset,
        address _flFactory,
        address _clFactory,
        uint256[5] memory specs,
        address[3] memory calcs
    )
        FDT(
            string(abi.encodePacked("Maple Loan Token")),
            string(abi.encodePacked("MPL-LOAN")),
            _liquidityAsset
        )
        public
    {
        IGlobals globals = _globals(msg.sender);

        // Perform validity cross-checks
        require(globals.isValidLiquidityAsset(_liquidityAsset),   "Loan:INVALID_LIQUIDITY_ASSET");
        require(globals.isValidCollateralAsset(_collateralAsset), "Loan:INVALID_COLLATERAL_ASSET");

        require(specs[2] != uint256(0),               "Loan:PID_EQ_ZERO");
        require(specs[1].mod(specs[2]) == uint256(0), "Loan:INVALID_TERM_DAYS");
        require(specs[3] > uint256(0),                "Loan:REQUEST_AMT_EQ_ZERO");

        borrower        = _borrower;
        liquidityAsset  = IERC20(_liquidityAsset);
        collateralAsset = IERC20(_collateralAsset);
        flFactory       = _flFactory;
        clFactory       = _clFactory;
        createdAt       = block.timestamp;

        // Update state variables
        apr                    = specs[0];
        termDays               = specs[1];
        paymentsRemaining      = specs[1].div(specs[2]);
        paymentIntervalSeconds = specs[2].mul(1 days);
        requestAmount          = specs[3];
        collateralRatio        = specs[4];
        fundingPeriod          = globals.fundingPeriod();
        defaultGracePeriod     = globals.defaultGracePeriod();
        repaymentCalc          = calcs[0];
        lateFeeCalc            = calcs[1];
        premiumCalc            = calcs[2];
        superFactory           = msg.sender;

        // Deploy lockers
        collateralLocker = ICollateralLockerFactory(_clFactory).newLocker(_collateralAsset);
        fundingLocker    = IFundingLockerFactory(_flFactory).newLocker(_liquidityAsset);
        emit LoanStateChanged(State.Ready);
    }

    /**************************/
    /*** Borrower Functions ***/
    /**************************/

    /**
        @dev Drawdown funding from FundingLocker, post collateral, and transition loanState from `Ready` to `Active`.
        @param amt Amount of liquidityAsset borrower draws down, remainder is returned to Loan where it can be claimed back by LoanFDT holders.
    */
    function drawdown(uint256 amt) external {
        _whenProtocolNotPaused();
        _isValidBorrower();
        _isValidState(State.Ready);
        IGlobals globals = _globals(superFactory);

        IFundingLocker _fundingLocker = IFundingLocker(fundingLocker);

        require(amt >= requestAmount,              "Loan:AMT_LT_REQUEST_AMT");
        require(amt <= _getFundingLockerBalance(), "Loan:AMT_GT_FUNDED_AMT");

        // Update accounting variables for Loan
        principalOwed  = amt;
        nextPaymentDue = block.timestamp.add(paymentIntervalSeconds);

        loanState = State.Active;

        // Transfer the required amount of collateral for drawdown from Borrower to CollateralLocker.
        collateralAsset.safeTransferFrom(borrower, collateralLocker, collateralRequiredForDrawdown(amt));

        // Transfer funding amount from FundingLocker to Borrower, then drain remaining funds to Loan.
        uint256 treasuryFee = globals.treasuryFee();
        uint256 investorFee = globals.investorFee();

        address treasury = globals.mapleTreasury();

        uint256 _feePaid = feePaid = amt.mul(investorFee).div(10_000);  // Update fees paid for `claim()`
        uint256 treasuryAmt        = amt.mul(treasuryFee).div(10_000);  // Calculate amt to send to MapleTreasury

        _transferFunds(_fundingLocker, treasury, treasuryAmt);                         // Send `treasuryFee` directly to `MapleTreasury`
        _transferFunds(_fundingLocker, borrower, amt.sub(treasuryAmt).sub(_feePaid));  // Transfer drawdown amount to Borrower

        // Update excessReturned for claim()
        excessReturned = _getFundingLockerBalance().sub(_feePaid);

        // Drain remaining funds from FundingLocker (amount equal to excessReturned plus feePaid)
        _fundingLocker.drain();

        // Call updateFundsReceived() update FDT accounting with funds recieved from fees and excess returned
        updateFundsReceived();

        _emitBalanceUpdateEventForCollateralLocker();
        _emitBalanceUpdateEventForFundingLocker();
        _emitBalanceUpdateEventForLoan();

        emit BalanceUpdated(treasury, address(liquidityAsset), liquidityAsset.balanceOf(treasury));
        emit LoanStateChanged(State.Active);
        emit Drawdown(amt);
    }

    /**
        @dev Make a payment for the Loan. Amounts are calculated for the borrower.
    */
    function makePayment() external {
        _whenProtocolNotPaused();
        _isValidState(State.Active);
        (uint256 total, uint256 principal, uint256 interest,, bool paymentLate) = getNextPayment();
        paymentsRemaining--;
        _makePayment(total, principal, interest, paymentLate);
    }

    /**
        @dev Make the full payment for this loan, a.k.a. "calling" the loan. This requires the borrower to pay a premium fee.
    */
    function makeFullPayment() public {
        _whenProtocolNotPaused();
        _isValidState(State.Active);
        (uint256 total, uint256 principal, uint256 interest) = getFullPayment();
        paymentsRemaining = uint256(0);
        _makePayment(total, principal, interest, false);
    }

    /**
        @dev Internal function to update the payment variables and transfer funds from the borrower into the Loan.
    */
    function _makePayment(uint256 total, uint256 principal, uint256 interest, bool paymentLate) internal {

        // Caching to reduce `SLOADs`
        uint256 _paymentsRemaining = paymentsRemaining;

        // Update internal accounting variables
        interestPaid = interestPaid.add(interest);
        if (principal > uint256(0)) principalPaid = principalPaid.add(principal);

        if (_paymentsRemaining > uint256(0)) {
            // Update info related to next payment, decrement principalOwed if needed
            nextPaymentDue = nextPaymentDue.add(paymentIntervalSeconds);
            if (principal > uint256(0)) principalOwed = principalOwed.sub(principal);
        } else {
            // Update info to close loan
            principalOwed  = uint256(0);
            loanState      = State.Matured;
            nextPaymentDue = uint256(0);

            // Transfer all collateral back to the borrower
            ICollateralLocker(collateralLocker).pull(borrower, _getCollateralLockerBalance());
            _emitBalanceUpdateEventForCollateralLocker();
            emit LoanStateChanged(State.Matured);
        }

        // Loan payer sends funds to loan
        liquidityAsset.safeTransferFrom(msg.sender, address(this), total);

        // Call updateFundsReceived() update FDT accounting with funds recieved from interest payment
        updateFundsReceived();

        emit PaymentMade(
            total,
            principal,
            interest,
            _paymentsRemaining,
            principalOwed,
            _paymentsRemaining > 0 ? nextPaymentDue : 0,
            paymentLate
        );

        _emitBalanceUpdateEventForLoan();
    }

    /************************/
    /*** Lender Functions ***/
    /************************/

    /**
        @dev Fund this loan and mint LoanFDTs for mintTo (DebtLocker in the case of Pool funding)
        @param  amt    Amount to fund the loan
        @param  mintTo Address that LoanFDTs are minted to
    */
    function fundLoan(address mintTo, uint256 amt) whenNotPaused external {
        _whenProtocolNotPaused();
        _isValidState(State.Ready);
        _isValidPool();
        _isWithinFundingPeriod();
        liquidityAsset.safeTransferFrom(msg.sender, fundingLocker, amt);

        uint256 wad = _toWad(amt);  // Convert to WAD precision
        _mint(mintTo, wad);         // Mint FDT to `mintTo` i.e DebtLocker contract.

        emit LoanFunded(amt, mintTo);
        _emitBalanceUpdateEventForFundingLocker();
    }

    /**
        @dev If the borrower has not drawn down on the Loan past the drawdown grace period, return capital to Loan,
             where it can be claimed back by LoanFDT holders.
    */
    function unwind() external {
        _whenProtocolNotPaused();
        _isValidState(State.Ready);

        // Update accounting for claim(), transfer funds from FundingLocker to Loan
        excessReturned = LoanLib.unwind(liquidityAsset, superFactory, fundingLocker, createdAt);

        updateFundsReceived();

        // Transition state to Expired
        loanState = State.Expired;
        emit LoanStateChanged(State.Expired);
    }

    /**
        @dev Trigger a default if a Loan is in a condition where a default can be triggered, liquidating all collateral and updating accounting.
    */
    function triggerDefault() external {
        _whenProtocolNotPaused();
        _isValidState(State.Active);
        require(LoanLib.canTriggerDefault(nextPaymentDue, defaultGracePeriod, superFactory, balanceOf(msg.sender), totalSupply()), "Loan:FAILED_TO_LIQUIDATE");

        // Pull collateralAsset from CollateralLocker, swap to liquidityAsset, and hold custody of resulting liquidityAsset in Loan
        (amountLiquidated, amountRecovered) = LoanLib.liquidateCollateral(collateralAsset, address(liquidityAsset), superFactory, collateralLocker);

        // Decrement principalOwed by amountRecovered, set defaultSuffered to the difference (shortfall from liquidation)
        if (amountRecovered <= principalOwed) {
            principalOwed   = principalOwed.sub(amountRecovered);
            defaultSuffered = principalOwed;
        }
        // Set principalOwed to zero and return excess value from liquidation back to borrower
        else {
            liquidationExcess = amountRecovered.sub(principalOwed);
            principalOwed = 0;
            liquidityAsset.safeTransfer(borrower, liquidationExcess); // Send excess to Borrower
        }

        // Call updateFundsReceived() update FDT accounting with funds recieved from liquidation
        updateFundsReceived();

        // Transition loanState to Liquidated
        loanState = State.Liquidated;

        // Emit liquidation event
        emit Liquidation(
            amountLiquidated,  // Amount of collateralAsset swapped
            amountRecovered,   // Amount of liquidityAsset recovered from swap
            liquidationExcess, // Amount of liquidityAsset returned to borrower
            defaultSuffered    // Remaining losses after liquidation
        );
        emit LoanStateChanged(State.Liquidated);
    }

    /***********************/
    /*** Admin Functions ***/
    /***********************/

    /**
        @dev Triggers paused state. Halts functionality for certain functions.
    */
    function pause() external {
        _isValidBorrowerOrAdmin();
        super._pause();
    }

    /**
        @dev Triggers unpaused state. Returns functionality for certain functions.
    */
    function unpause() external {
        _isValidBorrowerOrAdmin();
        super._unpause();
    }

    /**
        @dev Set admin.
        @param newAdmin New admin address
        @param allowed  Status of an admin
    */
    function setAdmin(address newAdmin, bool allowed) external {
        _whenProtocolNotPaused();
        _isValidBorrower();
        admins[newAdmin] = allowed;
    }

    /**************************/
    /*** Governor Functions ***/
    /**************************/

    /**
        @dev Transfer any locked funds to the governor.
        @param token Address of the token that need to reclaimed.
     */
    function reclaimERC20(address token) external {
        LoanLib.reclaimERC20(token, address(liquidityAsset), _globals(superFactory));
    }

    /*********************/
    /*** FDT Functions ***/
    /*********************/

    /**
        @dev Withdraws all available funds earned through FDT for a token holder.
    */
    function withdrawFunds() public override {
        _whenProtocolNotPaused();
        super.withdrawFunds();
    }

    /************************/
    /*** Getter Functions ***/
    /************************/

    /**
        @dev Public getter to know how much minimum amount of loan asset will get by swapping collateral asset.
        @return Expected amount of liquidityAsset to be recovered from liquidation based on current oracle prices
    */
    function getExpectedAmountRecovered() public view returns(uint256) {
        uint256 liquidationAmt = _getCollateralLockerBalance();
        return Util.calcMinAmount(_globals(superFactory), address(collateralAsset), address(liquidityAsset), liquidationAmt);
    }

    /**
        @dev Returns information on next payment amount.
        @return [0] = Entitiled interest to the next payment, Principal + Interest only when the next payment is last payment of the loan
                [1] = Entitiled principal amount needs to pay in the next payment
                [2] = Entitiled interest amount needs to pay in the next payment
                [3] = Payment Due Date
                [4] = Is Payment Late
    */
    function getNextPayment() public view returns(uint256, uint256, uint256, uint256, bool) {
        return LoanLib.getNextPayment(superFactory, repaymentCalc, nextPaymentDue, lateFeeCalc);
    }

    /**
        @dev Returns information on full payment amount.
        @return total     Principal and interest owed, combined
        @return principal Principal owed
        @return interest  Interest owed
    */
    function getFullPayment() public view returns(uint256 total, uint256 principal, uint256 interest) {
        (total, principal, interest) = IPremiumCalc(premiumCalc).getPremiumPayment(address(this));
    }

    /**
        @dev Helper for calculating collateral required to draw down amt.
        @param  amt The amount of liquidityAsset to draw down from FundingLocker
        @return The amount of collateralAsset required to post in CollateralLocker for given drawdown amt.
    */
    function collateralRequiredForDrawdown(uint256 amt) public view returns(uint256) {
        return LoanLib.collateralRequiredForDrawdown(
            IERC20Details(address(collateralAsset)),
            IERC20Details(address(liquidityAsset)),
            collateralRatio,
            superFactory,
            amt
        );
    }

    /************************/
    /*** Helper Functions ***/
    /************************/

    /**
        @dev Function to block functionality of functions when protocol is in a paused state.
    */
    function _whenProtocolNotPaused() internal {
        require(!_globals(superFactory).protocolPaused(), "Loan:PROTOCOL_PAUSED");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidBorrowerOrAdmin() internal {
        require(msg.sender == borrower || admins[msg.sender], "Pool:UNAUTHORIZED");
    }

    /**
        @dev Utility to convert to WAD precision.
    */
    function _toWad(uint256 amt) internal view returns(uint256) {
        return amt.mul(10 ** 18).div(10 ** IERC20Details(address(liquidityAsset)).decimals());
    }

    /**
        @dev Utility to return MapleGlobals interface.
    */
    function _globals(address loanFactory) internal view returns (IGlobals) {
        return IGlobals(ILoanFactory(loanFactory).globals());
    }

    /**
        @dev Utility to return CollateralLocker balance.
    */
    function _getCollateralLockerBalance() internal view returns (uint256) {
        return collateralAsset.balanceOf(collateralLocker);
    }

    /**
        @dev Utility to return FundingLocker balance.
    */
    function _getFundingLockerBalance() internal view returns (uint256) {
        return liquidityAsset.balanceOf(fundingLocker);
    }

    /**
        @dev Utility to check current state of Loan againt provided state.
        @param _state Enum of desired Loan state
    */
    function _isValidState(State _state) internal view {
        require(loanState == _state, "Loan:INVALID_STATE");
    }

    /**
        @dev Utility to return if msg.sender is the Loan borrower.
    */
    function _isValidBorrower() internal view {
        require(msg.sender == borrower, "Loan:INVALID_BORROWER");
    }

    /**
        @dev Utility to return if lender is using an approved Pool to fund the loan.
    */
    function _isValidPool() internal view {
        address pool        = ILiquidityLocker(msg.sender).pool();
        address poolFactory = IPool(pool).superFactory();
        require(
            _globals(superFactory).isValidPoolFactory(poolFactory) &&
            IPoolFactory(poolFactory).isPool(pool),
            "Loan:INVALID_LENDER"
        );
    }

    /**
        @dev Utility to ensure currently within the funding period.
    */
    function _isWithinFundingPeriod() internal view {
        require(block.timestamp <= createdAt.add(fundingPeriod), "Loan:PAST_FUNDING_PERIOD");
    }

    /**
        @dev Utility to transfer funds from the FundingLocker.
        @param from  Interface of the FundingLocker
        @param to    Address to send funds to
        @param value Amount to send
    */
    function _transferFunds(IFundingLocker from, address to, uint256 value) internal {
        from.pull(to, value);
    }

    /**
        @dev Utility to emit BalanceUpdated event for Loan.
    */
    function _emitBalanceUpdateEventForLoan() internal {
        emit BalanceUpdated(address(this), address(liquidityAsset), liquidityAsset.balanceOf(address(this)));
    }

    /**
        @dev Utility to emit BalanceUpdated event for FundingLocker.
    */
    function _emitBalanceUpdateEventForFundingLocker() internal {
        emit BalanceUpdated(fundingLocker, address(liquidityAsset), _getFundingLockerBalance());
    }

    /**
        @dev Utility to emit BalanceUpdated event for CollateralLocker.
    */
    function _emitBalanceUpdateEventForCollateralLocker() internal {
        emit BalanceUpdated(collateralLocker, address(collateralAsset), _getCollateralLockerBalance());
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./Loan.sol";

import "lib/openzeppelin-contracts/contracts/utils/Pausable.sol";

/// @title LoanFactory instantiates Loans.
contract LoanFactory is Pausable {

    using SafeMath for uint256;

    uint8 public constant CL_FACTORY = 0;  // Factory type of `CollateralLockerFactory`
    uint8 public constant FL_FACTORY = 2;  // Factory type of `FundingLockerFactory`

    uint8 public constant INTEREST_CALC_TYPE = 10;  // Calc type of `RepaymentCalc`
    uint8 public constant LATEFEE_CALC_TYPE  = 11;  // Calc type of `LateFeeCalc`
    uint8 public constant PREMIUM_CALC_TYPE  = 12;  // Calc type of `PremiumCalc`

    IGlobals public globals;  // Interface of MapleGlobals

    uint256 public loansCreated;  // Incrementor for number of loan vaults created.

    mapping(uint256 => address) public loans;   // Loans address mapping
    mapping(address => bool)    public isLoan;  // Used to check if a Loan was instantiated from this contract

    mapping(address => bool) public admins;  // Admin addresses that have permission to do certain operations in case of disaster mgt

    event LoanCreated(
        address loan,
        address indexed borrower,
        address indexed liquidityAsset,
        address collateralAsset,
        address collateralLocker,
        address fundingLocker,
        uint256[5] specs,
        address[3] calcs,
        string name,
        string symbol
    );

    constructor(address _globals) public {
        globals = IGlobals(_globals);
    }

    /**
        @dev Update the MapleGlobals contract
        @param newGlobals Address of new MapleGlobals contract
    */
    function setGlobals(address newGlobals) external {
        _isValidGovernor();
        globals = IGlobals(newGlobals);
    }

    /**
        @dev Create a new Loan.
        @param  liquidityAsset  Asset the loan will raise funding in
        @param  collateralAsset Asset the loan will use as collateral
        @param  flFactory       The factory to instantiate a FundingLocker from
        @param  clFactory       The factory to instantiate a CollateralLocker from
        @param  specs           Contains specifications for this loan
                specs[0] = apr
                specs[1] = termDays
                specs[2] = paymentIntervalDays
                specs[3] = requestAmount
                specs[4] = collateralRatio
        @param  calcs The calculators used for the loan.
                calcs[0] = repaymentCalc
                calcs[1] = lateFeeCalc
                calcs[2] = premiumCalc
        @return Address of the instantiated Loan.
    */
    function createLoan(
        address liquidityAsset,
        address collateralAsset,
        address flFactory,
        address clFactory,
        uint256[5] memory specs,
        address[3] memory calcs
    ) external whenNotPaused returns (address) {
        _whenProtocolNotPaused();
        IGlobals _globals = globals;

        // Validity checks
        require(_globals.isValidSubFactory(address(this), flFactory, FL_FACTORY), "LF:INVALID_FL_FACTORY");
        require(_globals.isValidSubFactory(address(this), clFactory, CL_FACTORY), "LF:INVALID_CL_FACTORY");

        require(_globals.isValidCalc(calcs[0], INTEREST_CALC_TYPE), "LF:INVALID_INTEREST_CALC");
        require(_globals.isValidCalc(calcs[1],  LATEFEE_CALC_TYPE), "LF:INVALID_LATE_FEE_CALC");
        require(_globals.isValidCalc(calcs[2],  PREMIUM_CALC_TYPE), "LF:INVALID_PREMIUM_CALC");

        // Deploy new Loan
        Loan loan = new Loan(
            msg.sender,
            liquidityAsset,
            collateralAsset,
            flFactory,
            clFactory,
            specs,
            calcs
        );

        // Update LoanFactory identification mappings
        loans[loansCreated]   = address(loan);
        isLoan[address(loan)] = true;
        loansCreated++;

        emit LoanCreated(
            address(loan),
            msg.sender,
            liquidityAsset,
            collateralAsset,
            loan.collateralLocker(),
            loan.fundingLocker(),
            specs,
            calcs,
            loan.name(),
            loan.symbol()
        );
        return address(loan);
    }

    /**
        @dev Set admin.
        @param newAdmin New admin address
        @param allowed  Status of an admin
    */
    function setAdmin(address newAdmin, bool allowed) external {
        _isValidGovernor();
        admins[newAdmin] = allowed;
    }

    /**
        @dev Triggers paused state. Halts functionality for certain functions. Only Governor can call this function.
    */
    function pause() external {
        _isValidGovernorOrAdmin();
        super._pause();
    }

    /**
        @dev Triggers unpaused state. Returns functionality for certain functions. Only Governor can call this function.
    */
    function unpause() external {
        _isValidGovernorOrAdmin();
        super._unpause();
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidGovernor() internal view {
        require(msg.sender == globals.governor(), "PoolFactory:INVALID_GOVERNOR");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidGovernorOrAdmin() internal {
        require(msg.sender == globals.governor() || admins[msg.sender], "PoolFactory:UNAUTHORIZED");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _whenProtocolNotPaused() internal {
        require(!globals.protocolPaused(), "PoolFactory:PROTOCOL_PAUSED");
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;
pragma experimental ABIEncoderV2;

import "./interfaces/IERC20Details.sol";
import "./interfaces/IPriceFeed.sol";
import "./interfaces/IOracle.sol";
import "./interfaces/ISubFactory.sol";

interface ICalc { function calcType() external view returns (uint8); }

/// @title MapleGlobals maintains a central source of parameters and allowlists for the Maple protocol.
contract MapleGlobals {

    address public immutable mpl;         // Maple Token is the ERC-2222 token for the Maple protocol

    address public pendingGovernor;       // Governor that is declared for transfer, must be accepted for transfer to take effect
    address public governor;              // Governor is responsible for management of global Maple variables
    address public mapleTreasury;         // Maple Treasury is the Treasury which all fees pass through for conversion, prior to distribution
    address public admin;                 // Admin of the whole network, has the power to switch off/on the functionality of entire protocol

    uint256 public defaultGracePeriod;    // Represents the amount of time a borrower has to make a missed payment before a default can be triggered
    uint256 public swapOutRequired;       // Represents minimum amount of Pool cover that a Pool Delegate has to provide before they can finalize a Pool
    uint256 public fundingPeriod;         // Amount of time to allow borrower to drawdown on their loan after funding period ends
    uint256 public investorFee;           // Portion of drawdown that goes to Pool Delegates/individual lenders
    uint256 public treasuryFee;           // Portion of drawdown that goes to MapleTreasury
    uint256 public maxSwapSlippage;       // Maximum amount of slippage for Uniswap transactions
    uint256 public minLoanEquity;         // Minimum amount of LoanFDTs required to trigger liquidations (basis points percentage of totalSupply)
    uint256 public stakerCooldownPeriod;  // Period (in secs) after which stakers are allowed to unstake  their BPTs  from the StakeLocker contract
    uint256 public lpCooldownPeriod;      // Period (in secs) after which LPs     are allowed to withdraw their funds from the Pool contract
    uint256 public stakerUnstakeWindow;   // Window of time (in secs) after `stakerCooldownPeriod` that a user has to withdraw before their intent to unstake  is invalidated
    uint256 public lpWithdrawWindow;      // Window of time (in secs) after `lpCooldownPeriod`     that a user has to withdraw before their intent to withdraw is invalidated


    bool public protocolPaused;  // Switch to pause the functionality of the entire protocol

    mapping(address => bool) public isValidLiquidityAsset;            // Mapping of valid liquidityAssets
    mapping(address => bool) public isValidCollateralAsset;           // Mapping of valid collateralAssets
    mapping(address => bool) public validCalcs;                       // Mapping of valid calculator contracts
    mapping(address => bool) public isValidPoolDelegate;              // Validation data structure for Pool Delegates (prevent invalid addresses from creating pools)
    mapping(address => bool) public isExemptFromTransferRestriction;  // Validation of if address is exempt from FDT transfer restrictions (cooldown + lockup)
    mapping(address => bool) public isValidBalancerPool;              // Validation of if address is a Balancer Pool that Maple has approved for BPT staking

    // Determines the liquidation path of various assets in Loans and Treasury.
    // The value provided will determine whether or not to perform a bilateral or triangular swap on Uniswap.
    // For example, defaultUniswapPath[WBTC][USDC] value would indicate what asset to convert WBTC into before
    // conversion to USDC. If defaultUniswapPath[WBTC][USDC] == USDC, then the swap is bilateral and no middle
    // asset is swapped.   If defaultUniswapPath[WBTC][USDC] == WETH, then swap WBTC for WETH, then WETH for USDC.
    mapping(address => mapping(address => address)) public defaultUniswapPath;

    mapping(address => address) public oracleFor;  // Chainlink oracle for a given asset

    mapping(address => bool)                     public isValidPoolFactory;  // Mapping of valid pool factories
    mapping(address => bool)                     public isValidLoanFactory;  // Mapping of valid loan factories
    mapping(address => mapping(address => bool)) public validSubFactories;   // Mapping of valid sub factories

    event              CollateralAssetSet(address asset, uint256 decimals, string symbol, bool valid);
    event               LiquidityAssetSet(address asset, uint256 decimals, string symbol, bool valid);
    event                       OracleSet(address asset, address oracle);
    event TransferRestrictionExemptionSet(address indexed exemptedContract, bool valid);
    event                 BalancerPoolSet(address balancerPool,   bool valid);
    event              PendingGovernorSet(address pendingGovernor);
    event                GovernorAccepted(address governor);
    event                 GlobalsParamSet(bytes32 indexed which, uint256 value);
    event               GlobalsAddressSet(bytes32 indexed which, address addr);
    event                  ProtocolPaused(bool pause);

    modifier isGovernor() {
        require(msg.sender == governor, "MapleGlobals:MSG_SENDER_NOT_GOVERNOR");
        _;
    }

    /**
        @dev    Constructor function.
        @param  _governor Address of Governor
        @param  _mpl      Address of the ERC-2222 token for the Maple protocol
        @param  _admin    Address that takes care of protocol security switch
    */
    constructor(address _governor, address _mpl, address _admin) public {
        governor             = _governor;
        mpl                  = _mpl;
        swapOutRequired      = 10_000;     // $10,000 of Pool cover
        fundingPeriod        = 10 days;
        defaultGracePeriod   = 5 days;
        investorFee          = 50;         // 0.5%
        treasuryFee          = 50;         // 0.5%
        maxSwapSlippage      = 1000;       // 10 %
        minLoanEquity        = 2000;       // 20 %
        admin                = _admin;
        stakerCooldownPeriod = 10 days;
        lpCooldownPeriod     = 10 days;
        stakerUnstakeWindow  = 2 days;
        lpWithdrawWindow     = 2 days;
    }

    /************************/
    /*** Setter Functions ***/
    /************************/

    /**
        @dev Update the `stakerCooldownPeriod` state variable. This change will affect existing cool down period for the stakers who already intended to unstake.
        @param newCooldownPeriod New value for the cool down period.
     */
        function setStakerCooldownPeriod(uint256 newCooldownPeriod) external isGovernor {
        stakerCooldownPeriod = newCooldownPeriod;
        emit GlobalsParamSet("STAKER_COOLDOWN_PERIOD", newCooldownPeriod);
    }

    /**
        @dev Update the `lpCooldownPeriod` state variable. This change will affect existing cool down period for the LPs who already intended to withdraw.
        @param newCooldownPeriod New value for the cool down period.
     */
    function setLpCooldownPeriod(uint256 newCooldownPeriod) external isGovernor {
        lpCooldownPeriod = newCooldownPeriod;
        emit GlobalsParamSet("LP_COOLDOWN_PERIOD", newCooldownPeriod);
    }

    /**
        @dev Update the `stakerUnstakeWindow` state variable. This change will affect existing window for the stalers who already applied to unstake.
        @param newUnstakeWindow New value for the unstake window.
     */
    function setStakerUnstakeWindow(uint256 newUnstakeWindow) external isGovernor {
        stakerUnstakeWindow = newUnstakeWindow;
        emit GlobalsParamSet("STAKER_UNSTAKE_WINDOW", newUnstakeWindow);
    }

    /**
        @dev Update the `lpWithdrawWindow` state variable. This change will affect existing window for the LPs who already intended to withdraw.
        @param newLpWithdrawWindow New value for the withdraw window.
     */
    function setLpWithdrawWindow(uint256 newLpWithdrawWindow) external isGovernor {
        lpWithdrawWindow = newLpWithdrawWindow;
        emit GlobalsParamSet("LP_WITHDRAW_WINDOW", newLpWithdrawWindow);
    }

    /**
        @dev Update the allowed Uniswap slippage percentage, in basis points. Only Governor can call.
        @param newMaxSlippage New max slippage percentage (in basis points)
     */
    function setMaxSwapSlippage(uint256 newMaxSlippage) external isGovernor {
        _checkPercentageRange(newMaxSlippage);
        maxSwapSlippage = newMaxSlippage;
        emit GlobalsParamSet("MAX_SWAP_SLIPPAGE", newMaxSlippage);
    }

    /**
      @dev Set admin.
      @param newAdmin New admin address
     */
    function setAdmin(address newAdmin) external {
        require(msg.sender == governor && admin != address(0), "MapleGlobals:UNAUTHORIZED");
        require(!protocolPaused, "MapleGlobals:PROCOTOL_PAUSED");
        admin = newAdmin;
    }

    /**
        @dev Update the allowlist for contracts that will be excempt from transfer restrictions (lockup and cooldown).
        These addresses are reserved for DeFi composability such as yield farming, collateral-based lending on other platforms, etc.
        Only Governor can call.
        @param addr  Address of exempt contract.
        @param valid The new bool value for validating addr.
    */
    function setExemptFromTransferRestriction(address addr, bool valid) external isGovernor {
        isExemptFromTransferRestriction[addr] = valid;
        emit TransferRestrictionExemptionSet(addr, valid);
    }

    /**
        @dev Update the valid Balancer Pool mapping. Only Governor can call.
        @param balancerPool Address of Balancer Pool contract.
        @param valid        The new bool value for validating Balancer Pool.
    */
    function setValidBalancerPool(address balancerPool, bool valid) external isGovernor {
        isValidBalancerPool[balancerPool] = valid;
        emit BalancerPoolSet(balancerPool, valid);
    }

    /**
      @dev Pause/unpause the protocol. Only admin user can call.
      @param pause Boolean flag to switch externally facing functionality in the protocol on/off
     */
    function setProtocolPause(bool pause) external {
        require(msg.sender == admin, "MapleGlobals:UNAUTHORIZED");
        protocolPaused = pause;
        emit ProtocolPaused(pause);
    }

    /**
        @dev Update the valid PoolFactory mapping. Only Governor can call.
        @param poolFactory Address of PoolFactory
        @param valid       The new bool value for validating poolFactory
    */
    function setValidPoolFactory(address poolFactory, bool valid) external isGovernor {
        isValidPoolFactory[poolFactory] = valid;
    }

    /**
        @dev Update the valid LoanFactory mapping. Only Governor can call.
        @param loanFactory Address of LoanFactory
        @param valid       The new bool value for validating loanFactory.
    */
    function setValidLoanFactory(address loanFactory, bool valid) external isGovernor {
        isValidLoanFactory[loanFactory] = valid;
    }

    /**
        @dev Set the validity of a subFactory as it relates to a superFactory. Only Governor can call.
        @param superFactory The core factory (e.g. PoolFactory, LoanFactory)
        @param subFactory   The sub factory used by core factory (e.g. LiquidityLockerFactory)
        @param valid        The validity of subFactory within context of superFactory
    */
    function setValidSubFactory(address superFactory, address subFactory, bool valid) external isGovernor {
        require(isValidLoanFactory[superFactory] || isValidPoolFactory[superFactory], "MapleGlobals:SUPER_FACTORY_NOT_VALID");
        validSubFactories[superFactory][subFactory] = valid;
    }

    /**
        @dev Set the path to swap an asset through Uniswap. Only Governor can call.
        @param from Asset being swapped
        @param to   Final asset to receive **
        @param mid  Middle asset

        ** Set to == mid to enable a bilateral swap (single path swap).
           Set to != mid to enable a triangular swap (multi path swap).
    */
    function setDefaultUniswapPath(address from, address to, address mid) external isGovernor {
        defaultUniswapPath[from][to] = mid;
    }

    /**
        @dev Update validity of Pool Delegate (those allowed to create Pools). Only Governor can call.
        @param delegate Address to manage permissions for
        @param valid    New permissions of address
    */
    function setPoolDelegateAllowlist(address delegate, bool valid) external isGovernor {
        isValidPoolDelegate[delegate] = valid;
    }

    /**
        @dev Set the validity of an asset for collateral. Only Governor can call.
        @param asset The asset to assign validity to
        @param valid The new validity of asset as collateral
    */
    function setCollateralAsset(address asset, bool valid) external isGovernor {
        isValidCollateralAsset[asset] = valid;
        emit CollateralAssetSet(asset, IERC20Details(asset).decimals(), IERC20Details(asset).symbol(), valid);
    }

    /**
        @dev Set the validity of an asset for loans/liquidity in Pools. Only Governor can call.
        @param asset Address of the valid asset
        @param valid The new validity of asset for loans/liquidity in Pools
    */
    function setLiquidityAsset(address asset, bool valid) external isGovernor {
        isValidLiquidityAsset[asset] = valid;
        emit LiquidityAssetSet(asset, IERC20Details(asset).decimals(), IERC20Details(asset).symbol(), valid);
    }

    /**
        @dev Specifiy validity of a calculator contract. Only Governor can call.
        @param  calc  Calculator address
        @param  valid Validity of calculator
    */
    function setCalc(address calc, bool valid) external isGovernor {
        validCalcs[calc] = valid;
    }

    /**
        @dev Adjust investorFee (in basis points). Only Governor can call.
        @param _fee The fee, e.g., 50 = 0.50%
    */
    function setInvestorFee(uint256 _fee) external isGovernor {
        _checkPercentageRange(_fee);
        require(_fee + treasuryFee <= 10_000, "MapleGlobals:INVALID_INVESTOR_FEE");
        investorFee = _fee;
        emit GlobalsParamSet("INVESTOR_FEE", _fee);
    }

    /**
        @dev Adjust treasuryFee (in basis points). Only Governor can call.
        @param _fee The fee, e.g., 50 = 0.50%
    */
    function setTreasuryFee(uint256 _fee) external isGovernor {
        _checkPercentageRange(_fee);
        require(_fee + investorFee <= 10_000, "MapleGlobals:INVALID_TREASURY_FEE");
        treasuryFee = _fee;
        emit GlobalsParamSet("TREASURY_FEE", _fee);
    }

    /**
        @dev Set the MapleTreasury contract. Only Governor can call.
        @param _mapleTreasury New MapleTreasury address
    */
    function setMapleTreasury(address _mapleTreasury) external isGovernor {
        require(_mapleTreasury != address(0), "MapleGlobals:ZERO_ADDRESS");
        mapleTreasury = _mapleTreasury;
        emit GlobalsAddressSet("MAPLE_TREASURY", _mapleTreasury);
    }

    /**
        @dev Adjust defaultGracePeriod. Only Governor can call.
        @param _defaultGracePeriod Number of seconds to set the grace period to
    */
    function setDefaultGracePeriod(uint256 _defaultGracePeriod) external isGovernor {
        defaultGracePeriod = _defaultGracePeriod;
        emit GlobalsParamSet("DEFAULT_GRACE_PERIOD", _defaultGracePeriod);
    }

    /**
        @dev Adjust minLoanEquity. Only Governor can call.
        @param _minLoanEquity Min percentage of Loan equity an address must have to trigger liquidations.
    */
    function setMinLoanEquity(uint256 _minLoanEquity) external isGovernor {
        _checkPercentageRange(_minLoanEquity);
        minLoanEquity = _minLoanEquity;
        emit GlobalsParamSet("MIN_LOAN_EQUITY", _minLoanEquity);
    }

    /**
        @dev Adjust fundingPeriod. Only Governor can call.
        @param _fundingPeriod Number of seconds to set the drawdown grace period to
    */
    function setFundingPeriod(uint256 _fundingPeriod) external isGovernor {
        fundingPeriod = _fundingPeriod;
        emit GlobalsParamSet("FUNDING_PERIOD", _fundingPeriod);
    }

    /**
        @dev Adjust the minimum Pool cover required to finalize a Pool. Only Governor can call.
        @param amt The new minimum swap out required
    */
    function setSwapOutRequired(uint256 amt) external isGovernor {
        require(amt >= uint256(10_000), "MapleGlobals:SWAP_OUT_TOO_LOW");
        swapOutRequired = amt;
        emit GlobalsParamSet("SWAP_OUT_REQUIRED", amt);
    }

    /**
        @dev Update a price feed's oracle.
        @param asset  Asset to update price for
        @param oracle New oracle to use
    */
    function setPriceOracle(address asset, address oracle) external isGovernor {
        oracleFor[asset] = oracle;
        emit OracleSet(asset, oracle);
    }

    /************************************/
    /*** Transfer Ownership Functions ***/
    /************************************/

    /**
        @dev Set a new pending Governor. This address can become governor if they accept. Only Governor can call.
        @param _pendingGovernor Address of new Governor
    */
    function setPendingGovernor(address _pendingGovernor) external isGovernor {
        require(_pendingGovernor != address(0), "MapleGlobals:ZERO_ADDRESS_GOVERNOR");
        pendingGovernor = _pendingGovernor;
        emit PendingGovernorSet(_pendingGovernor);
    }

    /**
        @dev Accept the Governor position. Only PendingGovernor can call.
    */
    function acceptGovernor() external {
        require(msg.sender == pendingGovernor, "MapleGlobals:NOT_PENDING_GOVERNOR");
        governor = pendingGovernor;
        pendingGovernor = address(0);
        emit GovernorAccepted(governor);
    }

    /************************/
    /*** Getter Functions ***/
    /************************/

    /**
        @dev Fetch price for asset from Chainlink oracles.
        @param asset Asset to fetch price of
        @return Price of asset in USD
    */
    function getLatestPrice(address asset) external view returns (uint256) {
        return uint256(IOracle(oracleFor[asset]).getLatestPrice());
    }

    /**
        @dev Check the validity of a subFactory as it relates to a superFactory.
        @param superFactory The core factory (e.g. PoolFactory, LoanFactory)
        @param subFactory   The sub factory used by core factory (e.g. LiquidityLockerFactory)
        @param factoryType  The type expected for the subFactory. References listed below.
            0 = COLLATERAL_LOCKER_FACTORY
            1 = DEBT_LOCKER_FACTORY
            2 = FUNDING_LOCKER_FACTORY
            3 = LIQUIDUITY_LOCKER_FACTORY
            4 = STAKE_LOCKER_FACTORY
    */
    function isValidSubFactory(address superFactory, address subFactory, uint8 factoryType) external view returns(bool) {
        return validSubFactories[superFactory][subFactory] && ISubFactory(subFactory).factoryType() == factoryType;
    }

    /**
        @dev Check the validity of a calculator.
        @param calc     Calculator address
        @param calcType Calculator type
    */
    function isValidCalc(address calc, uint8 calcType) external view returns(bool) {
        return validCalcs[calc] && ICalc(calc).calcType() == calcType;
    }

    /************************/
    /*** Helper Functions ***/
    /************************/

    function _checkPercentageRange(uint256 percentage) internal {
        require(percentage >= uint256(0) && percentage <= uint256(10_000), "MapleGlobals:PCT_BOUND_CHECK");
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./library/Util.sol";
import "./interfaces/IGlobals.sol";
import "./interfaces/IMapleToken.sol";
import "./interfaces/IERC20Details.sol";
import "./interfaces/IUniswapRouter.sol";

import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";
import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title MapleTreasury earns revenue from Loans and distributes it to token holders and the Maple development team.
contract MapleTreasury {

    using SafeMath  for uint256;
    using SafeERC20 for IERC20;

    address public immutable mpl;            // MapleToken contract
    address public immutable fundsToken;     // fundsToken value in the MapleToken contract
    address public immutable uniswapRouter;  // Official UniswapV2 router contract
    address public           globals;        // MapleGlobals contract

    /**
        @dev Instantiates the MapleTreasury contract.
        @param  _mpl           MapleToken contract
        @param  _fundsToken    fundsToken of MapleToken contract
        @param  _uniswapRouter Official UniswapV2 router contract
        @param  _globals       MapleGlobals contract
    */
    constructor(
        address _mpl,
        address _fundsToken,
        address _uniswapRouter,
        address _globals
    ) public {
        mpl           = _mpl;
        fundsToken    = _fundsToken;
        uniswapRouter = _uniswapRouter;
        globals       = _globals;
    }

    event ERC20Conversion(address indexed asset, uint256 amountIn, uint256 amountOut);
    event DistributedToHolders(uint256 amount);
    event ERC20Reclaimed(address indexed asset, uint256 amount);
    event FundsTokenModified(address by, address newFundsToken);

    modifier isGovernor() {
        require(msg.sender == IGlobals(globals).governor(), "MapleTreasury:MSG_SENDER_NOT_GOVERNOR");
        _;
    }

    /**
        @dev Update the MapleGlobals contract. Only Governor can set
        @param newGlobals Address of new MapleGlobals contract
    */
    function setGlobals(address newGlobals) external isGovernor {
        globals = newGlobals;
    }

    /**
        @dev Reclaim treasury funds to the MapleDAO address. Only Governor can call.
        @param asset  Address of the token that need to be reclaimed from the treasury contract
        @param amount Amount to withdraw
    */
    function reclaimERC20(address asset, uint256 amount) isGovernor public {
        IERC20(asset).safeTransfer(msg.sender, amount);
        emit ERC20Reclaimed(asset, amount);
    }

    /**
        @dev Passes through the current fundsToken balance of the treasury to MapleToken, where it can be claimed by MPL holders.
    */
    function distributeToHolders() isGovernor public {
        IERC20 _fundsToken = IERC20(fundsToken);
        uint256 distributeAmount = _fundsToken.balanceOf(address(this));
        _fundsToken.safeTransfer(mpl, distributeAmount);
        IMapleToken(mpl).updateFundsReceived();
        emit DistributedToHolders(distributeAmount);
    }

    /**
        @dev Convert an ERC-20 asset through Uniswap to fundsToken.
        @param asset The ERC-20 asset to convert to fundsToken
    */
    function convertERC20(address asset) isGovernor public {
        require(asset != fundsToken, "MapleTreasury:ASSET_EQUALS_FUNDS_TOKEN");

        IGlobals _globals = IGlobals(globals);

        uint256 assetBalance = IERC20(asset).balanceOf(address(this));
        uint256 minAmount    = Util.calcMinAmount(_globals, asset, fundsToken, assetBalance);

        IERC20(asset).safeApprove(uniswapRouter, uint256(0));
        IERC20(asset).safeApprove(uniswapRouter, assetBalance);

        address uniswapAssetForPath = _globals.defaultUniswapPath(asset, fundsToken);
        bool middleAsset = uniswapAssetForPath != fundsToken && uniswapAssetForPath != address(0);

        address[] memory path = new address[](middleAsset ? 3 : 2);

        path[0] = asset;
        path[1] = middleAsset ? uniswapAssetForPath : fundsToken;

        if (middleAsset) path[2] = fundsToken;

        uint256[] memory returnAmounts = IUniswapRouter(uniswapRouter).swapExactTokensForTokens(
            assetBalance,
            minAmount.sub(minAmount.mul(_globals.maxSwapSlippage()).div(10_000)),
            path,
            address(this),
            block.timestamp
        );

        emit ERC20Conversion(asset, returnAmounts[0], returnAmounts[path.length - 1]);
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "lib/openzeppelin-contracts/contracts/access/Ownable.sol";
import "lib/openzeppelin-contracts/contracts/math/Math.sol";
import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";
import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

// https://docs.synthetix.io/contracts/source/contracts/stakingrewards
/// @title MplRewards Synthetix farming contract fork for liquidity mining.
contract MplRewards is Ownable {

    using SafeMath  for uint256;
    using SafeERC20 for IERC20;

    IERC20  public immutable rewardsToken;
    IERC20  public immutable stakingToken;

    uint256 public periodFinish;
    uint256 public rewardRate;
    uint256 public rewardsDuration;
    uint256 public lastUpdateTime;
    uint256 public rewardPerTokenStored;
    uint256 public lastPauseTime;
    bool    public paused;

    mapping(address => uint256) public userRewardPerTokenPaid;
    mapping(address => uint256) public rewards;

    uint256 private _totalSupply;

    mapping(address => uint256) private _balances;

    event RewardAdded(uint256 reward);
    event Staked(address indexed user, uint256 amount);
    event Withdrawn(address indexed user, uint256 amount);
    event RewardPaid(address indexed user, uint256 reward);
    event RewardsDurationUpdated(uint256 newDuration);
    event Recovered(address token, uint256 amount);
    event PauseChanged(bool isPaused);

    constructor(address _rewardsToken, address _stakingToken, address _owner) public {
        rewardsToken    = IERC20(_rewardsToken);
        stakingToken    = IERC20(_stakingToken);
        rewardsDuration = 7 days;
        transferOwnership(_owner);
    }

    function _updateReward(address account) internal {
        rewardPerTokenStored = rewardPerToken();
        lastUpdateTime       = lastTimeRewardApplicable();
        if (account != address(0)) {
            rewards[account] = earned(account);
            userRewardPerTokenPaid[account] = rewardPerTokenStored;
        }
    }

    function _notPaused() internal view {
        require(!paused, "REWARDS:CONTRACT_PAUSED");
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(address account) external view returns (uint256) {
        return _balances[account];
    }

    function lastTimeRewardApplicable() public view returns (uint256) {
        return Math.min(block.timestamp, periodFinish);
    }

    function rewardPerToken() public view returns (uint256) {
        if (_totalSupply == 0) return rewardPerTokenStored;
        return
            rewardPerTokenStored.add(
                lastTimeRewardApplicable().sub(lastUpdateTime).mul(rewardRate).mul(1e18).div(_totalSupply)
            );
    }

    function earned(address account) public view returns (uint256) {
        return _balances[account].mul(rewardPerToken().sub(userRewardPerTokenPaid[account])).div(1e18).add(rewards[account]);
    }

    function getRewardForDuration() external view returns (uint256) {
        return rewardRate.mul(rewardsDuration);
    }

    function stake(uint256 amount) external {
        _notPaused();
        _updateReward(msg.sender);
        require(amount > 0, "REWARDS:STAKE_EQ_ZERO");
        _totalSupply = _totalSupply.add(amount);
        _balances[msg.sender] = _balances[msg.sender].add(amount);
        stakingToken.safeTransferFrom(msg.sender, address(this), amount);
        emit Staked(msg.sender, amount);
    }

    function withdraw(uint256 amount) public {
        _notPaused();
        _updateReward(msg.sender);
        require(amount > 0, "REWARDS:WITHDRAW_EQ_ZERO");
        _totalSupply = _totalSupply.sub(amount);
        _balances[msg.sender] = _balances[msg.sender].sub(amount);
        stakingToken.safeTransfer(msg.sender, amount);
        emit Withdrawn(msg.sender, amount);
    }

    function getReward() public {
        _notPaused();
        _updateReward(msg.sender);
        uint256 reward = rewards[msg.sender];
        if (reward > 0) {
            rewards[msg.sender] = 0;
            rewardsToken.safeTransfer(msg.sender, reward);
            emit RewardPaid(msg.sender, reward);
        }
    }

    function exit() external {
        withdraw(_balances[msg.sender]);
        getReward();
    }

    function notifyRewardAmount(uint256 reward) external onlyOwner {
        _updateReward(address(0));
        if (block.timestamp >= periodFinish) {
            rewardRate = reward.div(rewardsDuration);
        } else {
            uint256 remaining = periodFinish.sub(block.timestamp);
            uint256 leftover  = remaining.mul(rewardRate);
            rewardRate        = reward.add(leftover).div(rewardsDuration);
        }

        // Ensure the provided reward amount is not more than the balance in the contract.
        // This keeps the reward rate in the right range, preventing overflows due to
        // very high values of rewardRate in the earned and rewardsPerToken functions;
        // Reward + leftover must be less than 2^256 / 10^18 to avoid overflow.
        uint balance = rewardsToken.balanceOf(address(this));
        require(rewardRate <= balance.div(rewardsDuration), "REWARDS:REWARD_TOO_HIGH");

        lastUpdateTime = block.timestamp;
        periodFinish   = block.timestamp.add(rewardsDuration);
        emit RewardAdded(reward);
    }

    // End rewards emission earlier
    function updatePeriodFinish(uint timestamp) external onlyOwner {
        _updateReward(address(0));
        periodFinish = timestamp;
    }

    // Added to support recovering LP Rewards from other systems such as BAL to be distributed to holders
    function recoverERC20(address tokenAddress, uint256 tokenAmount) external onlyOwner {
        require(tokenAddress != address(stakingToken), "REWARDS:CANNOT_RECOVER_STAKE_TOKEN");
        IERC20(tokenAddress).safeTransfer(owner(), tokenAmount);
        emit Recovered(tokenAddress, tokenAmount);
    }

    function setRewardsDuration(uint256 _rewardsDuration) external onlyOwner {
        require(block.timestamp > periodFinish, "REWARDS:PERIOD_NOT_FINISHED");
        rewardsDuration = _rewardsDuration;
        emit RewardsDurationUpdated(rewardsDuration);
    }

    /**
        @dev Change the paused state of the contract. Only the contract owner may call this.
    */
    function setPaused(bool _paused) external onlyOwner {
        // Ensure we're actually changing the state before we do anything
        require(_paused != paused, "MplRewards:ALREADY_IN_SAME_STATE");

        // Set our paused state.
        paused = _paused;

        // If applicable, set the last pause time.
        if (_paused) lastPauseTime = block.timestamp;

        // Let everyone know that our pause state has changed.
        emit PauseChanged(paused);
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./MplRewards.sol";
import "./interfaces/IGlobals.sol";

/// @title MplRewardsFactory instantiates MplRewards contracts.
contract MplRewardsFactory {

    IGlobals public globals;  // Address of globals contract used to retrieve current governor

    mapping(address => bool) public isMplRewards;  // True if MplRewards was created by this factory, otherwise false.

    event MplRewardsCreated(address indexed rewardsToken, address indexed stakingToken, address owner);

    constructor(address _globals) public {
        globals = IGlobals(_globals);
    }

    /**
        @dev Update the MapleGlobals contract
        @param _globals Address of new MapleGlobals contract
    */
    function setGlobals(address _globals) external {
        require(msg.sender == globals.governor());
        globals = IGlobals(_globals);
    }

    /**
        @dev Instantiate a MplRewards contract.
        @param rewardsToken Address of the rewardsToken (will always be MPL)
        @param stakingToken Address of the stakingToken (token used to stake to earn rewards)
                            (i.e., Pool address for PoolFDT mining, StakeLocker address for staked BPT mining)
        @return Address of the instantiated MplRewards
    */
    function createMplRewards(address rewardsToken, address stakingToken) external returns (address) {
        require(msg.sender == globals.governor(), "MplRewardsFactory:UNAUTHORIZED");
        address mplRewards       = address(new MplRewards(rewardsToken, stakingToken, msg.sender));
        isMplRewards[mplRewards] = true;

        emit MplRewardsCreated(rewardsToken, stakingToken, msg.sender);
        return mplRewards;
    }
}



// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./token/PoolFDT.sol";

import "./interfaces/IBPool.sol";
import "./interfaces/IDebtLocker.sol";
import "./interfaces/IGlobals.sol";
import "./interfaces/ILiquidityLocker.sol";
import "./interfaces/ILiquidityLockerFactory.sol";
import "./interfaces/ILoan.sol";
import "./interfaces/ILoanFactory.sol";
import "./interfaces/IPoolFactory.sol";
import "./interfaces/IStakeLocker.sol";
import "./interfaces/IStakeLockerFactory.sol";

import "./library/PoolLib.sol";

import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";

/// @title Pool maintains all accounting and functionality related to Pools.
contract Pool is PoolFDT {

    using SafeMath  for uint256;
    using SafeERC20 for IERC20;

    uint256 constant WAD = 10 ** 18;

    uint8 public constant DL_FACTORY = 1;  // Factory type of `DebtLockerFactory`

    IERC20  public immutable liquidityAsset;  // The asset deposited by lenders into the LiquidityLocker, for funding Loans

    address public immutable poolDelegate;     // Pool Delegate address, maintains full authority over the Pool
    address public immutable liquidityLocker;  // The LiquidityLocker owned by this contract
    address public immutable stakeAsset;       // The asset deposited by stakers into the StakeLocker (BPTs), for liquidation during default events
    address public immutable stakeLocker;      // Address of the StakeLocker, escrowing stakeAsset
    address public immutable superFactory;     // The factory that deployed this Loan

    uint256 private immutable liquidityAssetDecimals;  // decimals() precision for the liquidityAsset

    uint256 public           stakingFee;   // Fee for stakers   (in basis points)
    uint256 public immutable delegateFee;  // Fee for delegates (in basis points)

    uint256 public principalOut;  // Sum of all outstanding principal on Loans
    uint256 public liquidityCap;  // Amount of liquidity tokens accepted by the Pool
    uint256 public lockupPeriod;  // Period of time from a user's depositDate that they cannot withdraw any funds

    bool public openToPublic;  // Boolean opening Pool to public for LP deposits

    enum State { Initialized, Finalized, Deactivated }
    State public poolState;

    mapping(address => uint256)                     public depositDate;                // Used for withdraw penalty calculation
    mapping(address => mapping(address => address)) public debtLockers;                // Address of the `DebtLocker` contract corresponds to [Loan][DebtLockerFactory].
    mapping(address => bool)                        public admins;                     // Admin addresses who have permission to do certain operations in case of disaster mgt.
    mapping(address => bool)                        public allowedLiquidityProviders;  // Map that contains the list of address to enjoy the early access of the pool.
    mapping(address => uint256)                     public withdrawCooldown;           // Timestamp of when LP calls `intendToWithdraw()`

    event       LoanFunded(address indexed loan, address debtLocker, uint256 amountFunded);
    event            Claim(address indexed loan, uint256 interest, uint256 principal, uint256 fee);
    event   BalanceUpdated(address indexed who,  address token, uint256 balance);
    event  LPStatusChanged(address indexed user, bool status);
    event  LiquidityCapSet(uint256 newLiquidityCap);
    event  LockupPeriodSet(uint256 newLockupPeriod);
    event    StakingFeeSet(uint256 newStakingFee);
    event PoolStateChanged(State state);
    event         Cooldown(address indexed lp, uint256 cooldown);
    event  DefaultSuffered(
        address indexed loan,
        uint256 defaultSuffered,
        uint256 bptsBurned,
        uint256 bptsReturned,
        uint256 liquidityAssetRecoveredFromBurn
    );
    event  PoolOpenedToPublic(bool isOpen);

    /**
        Universal accounting law: fdtTotalSupply = liquidityLockerBal + principalOut - interestSum + poolLosses
               liquidityLockerBal + principalOut = fdtTotalSupply + interestSum - poolLosses
    */

    /**
        @dev Constructor for a Pool.
        @param  _poolDelegate   Address that has manager privileges of the Pool
        @param  _liquidityAsset Asset used to fund the Pool, It gets escrowed in `LiquidityLocker`
        @param  _stakeAsset     Asset escrowed in StakeLocker
        @param  _slFactory      Factory used to instantiate StakeLocker
        @param  _llFactory      Factory used to instantiate LiquidityLocker
        @param  _stakingFee     Fee that `stakers` earn on interest, in basis points
        @param  _delegateFee    Fee that `_poolDelegate` earns on interest, in basis points
        @param  _liquidityCap   Max amount of liquidityAsset accepted by the Pool
        @param  name            Name of Pool token
        @param  symbol          Symbol of Pool token
    */
    constructor(
        address _poolDelegate,
        address _liquidityAsset,
        address _stakeAsset,
        address _slFactory,
        address _llFactory,
        uint256 _stakingFee,
        uint256 _delegateFee,
        uint256 _liquidityCap,
        string memory name,
        string memory symbol
    ) PoolFDT(name, symbol) public {

        // Conduct sanity checks on Pool params
        PoolLib.poolSanityChecks(_globals(msg.sender), _liquidityAsset, _stakeAsset, _stakingFee, _delegateFee);

        // Assign variables relating to liquidityAsset
        liquidityAsset         = IERC20(_liquidityAsset);
        liquidityAssetDecimals = ERC20(_liquidityAsset).decimals();

        // Assign state variables
        stakeAsset   = _stakeAsset;
        poolDelegate = _poolDelegate;
        stakingFee   = _stakingFee;
        delegateFee  = _delegateFee;
        superFactory = msg.sender;
        liquidityCap = _liquidityCap;

        // Initialize the LiquidityLocker and StakeLocker
        stakeLocker     = address(IStakeLockerFactory(_slFactory).newLocker(_stakeAsset, _liquidityAsset));
        liquidityLocker = address(ILiquidityLockerFactory(_llFactory).newLocker(_liquidityAsset));

        lockupPeriod = 180 days;

        emit PoolStateChanged(State.Initialized);
    }

    /*******************************/
    /*** Pool Delegate Functions ***/
    /*******************************/

    /**
        @dev Finalize the Pool, enabling deposits. Checks Pool Delegate amount deposited to StakeLocker.
    */
    function finalize() external {
        _isValidDelegateAndProtocolNotPaused();
        _isValidState(State.Initialized);
        (,, bool stakeSufficient,,) = getInitialStakeRequirements();
        require(stakeSufficient, "Pool:INSUFFICIENT_STAKE");
        poolState = State.Finalized;
        emit PoolStateChanged(poolState);
    }

    /**
        @dev Fund a loan for amt, utilize the supplied dlFactory for debt lockers.
        @param  loan      Address of the loan to fund
        @param  dlFactory The DebtLockerFactory to utilize
        @param  amt       Amount to fund the loan
    */
    function fundLoan(address loan, address dlFactory, uint256 amt) external {
        _isValidDelegateAndProtocolNotPaused();
        _isValidState(State.Finalized);
        principalOut = principalOut.add(amt);
        PoolLib.fundLoan(debtLockers, superFactory, liquidityLocker, loan, dlFactory, amt);
        _emitBalanceUpdatedEvent();
    }

    /**
        @dev Liquidate the loan. Pool delegate could liquidate a loan only when loan completes its grace period.
        Pool delegate can claim its proportion of recovered funds from liquidation using the `claim()` function.
        @param loan      Address of the loan contract to liquidate
        @param dlFactory Address of the debt locker factory that is used to pull corresponding debt locker
     */
    function triggerDefault(address loan, address dlFactory) external {
        _isValidDelegateAndProtocolNotPaused();
        IDebtLocker(debtLockers[loan][dlFactory]).triggerDefault();
    }

    /**
        @dev Claim available funds for loan through specified DebtLockerFactory.
        @param  loan      Address of the loan to claim from
        @param  dlFactory The DebtLockerFactory (always maps to a single debt locker)
        @return [0] = Total amount claimed
                [1] = Interest  portion claimed
                [2] = Principal portion claimed
                [3] = Fee       portion claimed
                [4] = Excess    portion claimed
                [5] = Recovered portion claimed (from liquidations)
                [6] = Default suffered
    */
    function claim(address loan, address dlFactory) external returns(uint256[7] memory) {
        _whenProtocolNotPaused();
        _isValidDelegateOrAdmin();
        uint256[7] memory claimInfo = IDebtLocker(debtLockers[loan][dlFactory]).claim();

        (uint256 poolDelegatePortion, uint256 stakeLockerPortion, uint256 principalClaim, uint256 interestClaim) = PoolLib.calculateClaimAndPortions(claimInfo, delegateFee, stakingFee);

        // Subtract outstanding principal by principal claimed plus excess returned
        // Considers possible principalClaim overflow if liquidityAsset is transferred directly into Loan
        if (principalClaim <= principalOut) {
            principalOut = principalOut - principalClaim;
        } else {
            interestClaim  = interestClaim.add(principalClaim - principalOut);  // Distribute principalClaim overflow as interest to LPs
            principalClaim = principalOut;                                      // Set principalClaim to principalOut so correct amount gets transferred
            principalOut   = 0;                                                 // Set principalOut to zero to avoid subtraction overflow
        }

        // Accounts for rounding error in stakeLocker/poolDelegate/liquidityLocker interest split
        interestSum = interestSum.add(interestClaim);

        _transferLiquidityAsset(poolDelegate, poolDelegatePortion);  // Transfer fee and portion of interest to pool delegate
        _transferLiquidityAsset(stakeLocker,  stakeLockerPortion);   // Transfer portion of interest to stakeLocker

        // Transfer remaining claim (remaining interest + principal + excess + recovered) to liquidityLocker
        // Dust will accrue in Pool, but this ensures that state variables are in sync with liquidityLocker balance updates
        // Not using balanceOf in case of external address transferring liquidityAsset directly into Pool
        // Ensures that internal accounting is exactly reflective of balance change.
        _transferLiquidityAsset(liquidityLocker, principalClaim.add(interestClaim));

        // Handle default if defaultSuffered > 0
        if (claimInfo[6] > 0) _handleDefault(loan, claimInfo[6]);

        // Update funds received for StakeLockerFDTs
        IStakeLocker(stakeLocker).updateFundsReceived();

        // Update funds received for PoolFDTs
        updateFundsReceived();

        _emitBalanceUpdatedEvent();
        emit BalanceUpdated(stakeLocker, address(liquidityAsset), liquidityAsset.balanceOf(stakeLocker));

        emit Claim(loan, interestClaim, principalClaim, claimInfo[3]);  // TODO: Discuss with offchain team about requirements for event

        return claimInfo;  // TODO: Discuss with offchain team about requirements for return
    }

    /**
        @dev Helper function if a claim has been made and there is a non-zero defaultSuffered amount.
        @param loan            Address of loan that has defaulted
        @param defaultSuffered Losses suffered from default after liquidation
    */
    function _handleDefault(address loan, uint256 defaultSuffered) internal {

        (uint256 bptsBurned, uint256 postBurnBptBal, uint256 liquidityAssetRecoveredFromBurn) = PoolLib.handleDefault(liquidityAsset, stakeLocker, stakeAsset, loan, defaultSuffered);

        // If BPT burn is not enough to cover full default amount, pass on losses to LPs with PoolFDT loss accounting
        if (defaultSuffered > liquidityAssetRecoveredFromBurn) {
            poolLosses = poolLosses.add(defaultSuffered - liquidityAssetRecoveredFromBurn);
            updateLossesReceived();
        }

        // Transfer liquidityAsset from burn to liquidityLocker
        liquidityAsset.safeTransfer(liquidityLocker, liquidityAssetRecoveredFromBurn);

        principalOut = principalOut.sub(defaultSuffered);  // Subtract rest of Loan's principal from principalOut

        emit DefaultSuffered(
            loan,                            // Which loan defaultSuffered is from
            defaultSuffered,                 // Total default suffered from loan by Pool after liquidation
            bptsBurned,                      // Amount of BPTs burned from stakeLocker
            postBurnBptBal,                  // Remaining BPTs in stakeLocker post-burn
            liquidityAssetRecoveredFromBurn  // Amount of liquidityAsset recovered from burning BPTs
        );
    }

    /**
        @dev Pool Delegate triggers deactivation, permanently shutting down the pool. Must have less than 100 USD worth of liquidityAsset principalOut.
    */
    function deactivate() external {
        _isValidDelegateAndProtocolNotPaused();
        _isValidState(State.Finalized);
        PoolLib.validateDeactivation(_globals(superFactory), principalOut, address(liquidityAsset));
        poolState = State.Deactivated;
        emit PoolStateChanged(poolState);
    }

    /**************************************/
    /*** Pool Delegate Setter Functions ***/
    /**************************************/

    /**
        @dev Set `liquidityCap`, Only allowed by the Pool Delegate or the admin.
        @param newLiquidityCap New liquidityCap value
    */
    function setLiquidityCap(uint256 newLiquidityCap) external {
        _whenProtocolNotPaused();
        _isValidDelegateOrAdmin();
        liquidityCap = newLiquidityCap;
        emit LiquidityCapSet(newLiquidityCap);
    }

    /**
        @dev Set the lockup period. Only Pool Delegate can call this function.
        @param newLockupPeriod New lockup period used to restrict the withdrawals.
     */
    function setLockupPeriod(uint256 newLockupPeriod) external {
        _isValidDelegateAndProtocolNotPaused();
        require(newLockupPeriod <= lockupPeriod, "Pool:INVALID_VALUE");
        lockupPeriod = newLockupPeriod;
        emit LockupPeriodSet(newLockupPeriod);
    }

    /**
        @dev Update staking fee. Only Pool Delegate can call this function.
        @param newStakingFee New staking fee.
    */
    function setStakingFee(uint256 newStakingFee) external {
        _isValidDelegateAndProtocolNotPaused();
        require(newStakingFee.add(delegateFee) <= 10_000, "Pool:INVALID_FEE");
        stakingFee = newStakingFee;
        emit StakingFeeSet(newStakingFee);
    }

    /**
        @dev Update user status on Pool allowlist. Only Pool Delegate can call this function.
        @param user   The address to set status for.
        @param status The status of user on allowlist.
    */
    function setAllowList(address user, bool status) external {
        _isValidDelegateAndProtocolNotPaused();
        allowedLiquidityProviders[user] = status;
        emit LPStatusChanged(user, status);
    }

    /**
        @dev Update user status on StakeLocker allowlist. Only Pool Delegate can call this function.
        @param user   The address to set status for.
        @param status The status of user on allowlist.
    */
    function setAllowlistStakeLocker(address user, bool status) external {
        _isValidDelegateAndProtocolNotPaused();
        IStakeLocker(stakeLocker).setAllowlist(user, status);
    }

    /**
        @dev Set admin
        @param newAdmin new admin address.
        @param allowed Status of an admin.
    */
    function setAdmin(address newAdmin, bool allowed) external {
        _isValidDelegateAndProtocolNotPaused();
        admins[newAdmin] = allowed;
    }

    /**
        @dev Set public pool access. Only Pool Delegate can call this function.
        @param open Public pool access status.
    */
    function setOpenToPublic(bool open) external {
        _isValidDelegateAndProtocolNotPaused();
        openToPublic = open;
        emit PoolOpenedToPublic(open);
    }

    /************************************/
    /*** Liquidity Provider Functions ***/
    /************************************/

    /**
        @dev Liquidity providers can deposit liquidityAsset into the LiquidityLocker, minting FDTs.
        @param amt Amount of liquidityAsset to deposit
    */
    function deposit(uint256 amt) external {
        _whenProtocolNotPaused();
        _isValidState(State.Finalized);
        require(isDepositAllowed(amt), "Pool:NOT_ALLOWED");

        withdrawCooldown[msg.sender] = uint256(0);  // Reset withdrawCooldown if LP had previously intended to withdraw

        uint256 wad = _toWad(amt);
        PoolLib.updateDepositDate(depositDate, balanceOf(msg.sender), wad, msg.sender);

        liquidityAsset.safeTransferFrom(msg.sender, liquidityLocker, amt);
        _mint(msg.sender, wad);

        _emitBalanceUpdatedEvent();
        emit Cooldown(msg.sender, uint256(0));
    }

    /**
        @dev Activates the cooldown period to withdraw. It can't be called if the user is not providing liquidity.
    **/
    function intendToWithdraw() external {
        PoolLib.intendToWithdraw(withdrawCooldown, balanceOf(msg.sender));
    }

    /**
        @dev Cancels an initiated withdrawal by resetting withdrawCooldown.
    **/
    function cancelWithdraw() external {
        PoolLib.cancelWithdraw(withdrawCooldown);
    }

    /**
        @dev Liquidity providers can withdraw liquidityAsset from the LiquidityLocker, burning PoolFDTs.
        @param amt Amount of liquidityAsset to withdraw
    */
    function withdraw(uint256 amt) external {
        _whenProtocolNotPaused();
        uint256 wad = _toWad(amt);
        require(PoolLib.isWithdrawAllowed(withdrawCooldown[msg.sender], _globals(superFactory)), "Pool:WITHDRAW_NOT_ALLOWED");
        require(depositDate[msg.sender].add(lockupPeriod) <= block.timestamp,                    "Pool:FUNDS_LOCKED");

        _burn(msg.sender, wad);  // Burn the corresponding FDT balance
        withdrawFunds();         // Transfer full entitled interest, decrement `interestSum`

        // Transfer amount that is due after realized losses are accounted for.
        // recognizedLosses are absorbed by the LP.
        _transferLiquidityLockerFunds(msg.sender, amt.sub(recognizeLosses()));

        // TODO: Do we need PoolFDT BalanceUpdated events?
        _emitBalanceUpdatedEvent();
    }

    /**
        @dev Transfer PoolFDTs.
        @param from Address sending   PoolFDTs
        @param to   Address receiving PoolFDTs
        @param wad  Amount of PoolFDTs to transfer
    */
    function _transfer(address from, address to, uint256 wad) internal override {
        _whenProtocolNotPaused();
        PoolLib.prepareTransfer(withdrawCooldown, depositDate, from, to, wad, _globals(superFactory), balanceOf(to), recognizableLossesOf(from));
        super._transfer(from, to, wad);
    }

    /**
        @dev Withdraws all claimable interest from the `liquidityLocker` for a user using `interestSum` accounting.
    */
    function withdrawFunds() public override {
        _whenProtocolNotPaused();
        uint256 withdrawableFunds = _prepareWithdraw();

        if (withdrawableFunds > uint256(0)) {
            _transferLiquidityLockerFunds(msg.sender, withdrawableFunds);
            _emitBalanceUpdatedEvent();

            interestSum = interestSum.sub(withdrawableFunds);

            _updateFundsTokenBalance();
        }
    }

    /**************************/
    /*** Governor Functions ***/
    /**************************/

    /**
        @dev Transfer any locked funds to the governor.
        @param token Address of the token to reclaim.
    */
    function reclaimERC20(address token) external {
        PoolLib.reclaimERC20(token, address(liquidityAsset), _globals(superFactory));
    }

    /*************************/
    /*** Getter Functions ***/
    /*************************/

    /**
        @dev View claimable balance from LiqudityLocker (reflecting deposit + gain/loss).
        @param lp Liquidity Provider to check claimableFunds for
        @return total     Total     amount claimable
        @return principal Principal amount claimable
        @return interest  Interest  amount claimable
    */
    function claimableFunds(address lp) public view returns(uint256 total, uint256 principal, uint256 interest) {
        (total, principal, interest) =
            PoolLib.claimableFunds(
                withdrawableFundsOf(lp),
                depositDate[lp],
                lockupPeriod,
                balanceOf(lp),
                liquidityAssetDecimals
            );
    }

    /**
        @dev Calculates the value of BPT in units of liquidityAsset.
        @param _bPool          Address of Balancer pool
        @param _liquidityAsset Asset used by Pool for liquidity to fund loans
        @param _staker         Address that deposited BPTs to stakeLocker
        @param _stakeLocker    Escrows BPTs deposited by staker
        @return USDC value of staker BPTs
    */
    function BPTVal(
        address _bPool,
        address _liquidityAsset,
        address _staker,
        address _stakeLocker
    ) public view returns (uint256) {
        return PoolLib.BPTVal(_bPool, _liquidityAsset, _staker, _stakeLocker);
    }

    /**
        @dev Check whether the given `depositAmt` is acceptable based on current liquidityCap.
        @param depositAmt Amount of tokens (i.e liquidityAsset type) user is trying to deposit
    */
    function isDepositAllowed(uint256 depositAmt) public view returns(bool) {
        bool isValidLP = openToPublic || allowedLiquidityProviders[msg.sender];
        return _balanceOfLiquidityLocker().add(principalOut).add(depositAmt) <= liquidityCap && isValidLP;
    }

    /**
        @dev Returns information on the stake requirements.
        @return [0] = Min amount of liquidityAsset coverage from staking required
                [1] = Present amount of liquidityAsset coverage from Pool Delegate stake
                [2] = If enough stake is present from Pool Delegate for finalization
                [3] = Staked BPTs required for minimum liquidityAsset coverage
                [4] = Current staked BPTs
    */
    function getInitialStakeRequirements() public view returns (uint256, uint256, bool, uint256, uint256) {
        return PoolLib.getInitialStakeRequirements(_globals(superFactory), stakeAsset, address(liquidityAsset), poolDelegate, stakeLocker);
    }

    /**
        @dev Calculates BPTs required if burning BPTs for liquidityAsset, given supplied tokenAmountOutRequired.
        @param  _bPool                        Balancer pool that issues the BPTs
        @param  _liquidityAsset               Swap out asset (e.g. USDC) to receive when burning BPTs
        @param  _staker                       Address that deposited BPTs to stakeLocker
        @param  _stakeLocker                  Escrows BPTs deposited by staker
        @param  _liquidityAssetAmountRequired Amount of liquidityAsset required to recover
        @return [0] = poolAmountIn required
                [1] = poolAmountIn currently staked
    */
    function getPoolSharesRequired(
        address _bPool,
        address _liquidityAsset,
        address _staker,
        address _stakeLocker,
        uint256 _liquidityAssetAmountRequired
    ) external view returns (uint256, uint256) {
        return PoolLib.getPoolSharesRequired(_bPool, _liquidityAsset, _staker, _stakeLocker, _liquidityAssetAmountRequired);
    }

    /**
      @dev Checks whether pool state is `Finalized`?
      @return bool Boolean value indicating if Pool is in a Finalized state.
     */
    function isPoolFinalized() external view returns(bool) {
        return poolState == State.Finalized;
    }

    /************************/
    /*** Helper Functions ***/
    /************************/

    /**
        @dev Utility to convert to WAD precision.
        @param amt Amount to convert
    */
    function _toWad(uint256 amt) internal view returns(uint256) {
        return amt.mul(WAD).div(10 ** liquidityAssetDecimals);
    }

    /**
        @dev Fetch the balance of this Pool's LiquidityLocker.
        @return Balance of LiquidityLocker
    */
    function _balanceOfLiquidityLocker() internal view returns(uint256) {
        return liquidityAsset.balanceOf(liquidityLocker);
    }

    /**
        @dev Utility to check current state of Pool againt provided state.
        @param _state Enum of desired Pool state
    */
    function _isValidState(State _state) internal view {
        require(poolState == _state, "Pool:INVALID_STATE");
    }

    /**
        @dev Utility to return if msg.sender is the Pool Delegate.
    */
    function _isValidDelegate() internal view {
        require(msg.sender == poolDelegate, "Pool:INVALID_DELEGATE");
    }

    /**
        @dev Utility to return MapleGlobals interface.
    */
    function _globals(address poolFactory) internal view returns (IGlobals) {
        return IGlobals(IPoolFactory(poolFactory).globals());
    }

    /**
        @dev Utility to emit BalanceUpdated event for LiquidityLocker.
    */
    function _emitBalanceUpdatedEvent() internal {
        emit BalanceUpdated(liquidityLocker, address(liquidityAsset), _balanceOfLiquidityLocker());
    }

    /**
        @dev Transfers liquidity asset from address(this) to given `to` address.
        @param to    Address to transfer liquidityAsset
        @param value Amount of liquidity asset that gets transferred
    */
    function _transferLiquidityAsset(address to, uint256 value) internal {
        liquidityAsset.safeTransfer(to, value);
    }

    /**
        @dev Function to determine if msg.sender is eligible to setLiquidityCap for security reasons.
    */
    function _isValidDelegateOrAdmin() internal {
        require(msg.sender == poolDelegate || admins[msg.sender], "Pool:UNAUTHORIZED");
    }

    /**
        @dev Function to block functionality of functions when protocol is in a paused state.
    */
    function _whenProtocolNotPaused() internal {
        require(!_globals(superFactory).protocolPaused(), "Pool:PROTOCOL_PAUSED");
    }

    function _isValidDelegateAndProtocolNotPaused() internal {
        _isValidDelegate();
        _whenProtocolNotPaused();
    }

    function _transferLiquidityLockerFunds(address to, uint256 value) internal {
        ILiquidityLocker(liquidityLocker).transfer(to, value);
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./Pool.sol";

import "lib/openzeppelin-contracts/contracts/utils/Pausable.sol";

/// @title PoolFactory instantiates Pools.
contract PoolFactory is Pausable {

    uint8 public constant LL_FACTORY = 3;  // Factory type of `LiquidityLockerFactory`
    uint8 public constant SL_FACTORY = 4;  // Factory type of `StakeLockerFactory`

    uint256  public poolsCreated;  // Incrementor for number of Pools created
    IGlobals public globals;       // MapleGlobals contract

    mapping(uint256 => address) public pools;   // Map to keep `Pool` contract corresponds to its index.
    mapping(address => bool)    public isPool;  // Used to check if a `Pool` was instantiated from this factory.
    mapping(address => bool)    public admins;  // Admin addresses that have permission to do certain operations in case of disaster mgt

    event PoolCreated(
        address indexed pool,
        address indexed delegate,
        address liquidityAsset,
        address stakeAsset,
        address liquidityLocker,
        address stakeLocker,
        uint256 stakingFee,
        uint256 delegateFee,
        uint256 liquidityCap,
        string  name,
        string  symbol
    );

    constructor(address _globals) public {
        globals = IGlobals(_globals);
    }

    /**
        @dev Update the MapleGlobals contract
        @param newGlobals Address of new MapleGlobals contract
    */
    function setGlobals(address newGlobals) external {
        _isValidGovernor();
        globals = IGlobals(newGlobals);
    }

    /**
        @dev Instantiates a Pool contract.
        @param  liquidityAsset The asset escrowed in LiquidityLocker
        @param  stakeAsset     The asset escrowed in StakeLocker
        @param  slFactory      The factory to instantiate a StakeLocker from
        @param  llFactory      The factory to instantiate a LiquidityLocker from
        @param  stakingFee     Fee that stakers earn on interest, in basis points
        @param  delegateFee    Fee that pool delegate earns on interest, in basis points
        @param  liquidityCap   Amount of liquidityAsset accepted by the pool
    */
    function createPool(
        address liquidityAsset,
        address stakeAsset,
        address slFactory,
        address llFactory,
        uint256 stakingFee,
        uint256 delegateFee,
        uint256 liquidityCap
    ) public whenNotPaused returns (address) {
        _whenProtocolNotPaused();
        {
            IGlobals _globals = globals;
            require(_globals.isValidSubFactory(address(this), llFactory, LL_FACTORY), "PF:INVALID_LL_FACTORY");
            require(_globals.isValidSubFactory(address(this), slFactory, SL_FACTORY), "PF:INVALID_SL_FACTORY");
            require(_globals.isValidPoolDelegate(msg.sender),                         "PF:INVALID_DELEGATE");
        }

        string memory name   = string(abi.encodePacked("Maple Pool Token"));
        string memory symbol = string(abi.encodePacked("MPL-LP"));

        Pool pool =
            new Pool(
                msg.sender,
                liquidityAsset,
                stakeAsset,
                slFactory,
                llFactory,
                stakingFee,
                delegateFee,
                liquidityCap,
                name,
                symbol
            );

        pools[poolsCreated]   = address(pool);
        isPool[address(pool)] = true;
        poolsCreated++;

        emit PoolCreated(
            address(pool),
            msg.sender,
            liquidityAsset,
            stakeAsset,
            pool.liquidityLocker(),
            pool.stakeLocker(),
            stakingFee,
            delegateFee,
            liquidityCap,
            name,
            symbol
        );
        return address(pool);
    }

    /**
        @dev Set admin.
        @param newAdmin New admin address
        @param allowed  Status of an admin
    */
    function setAdmin(address newAdmin, bool allowed) external {
        _isValidGovernor();
        admins[newAdmin] = allowed;
    }

    /**
        @dev Triggers paused state. Halts functionality for certain functions. Only Governor can call this function.
    */
    function pause() external {
        _isValidGovernorOrAdmin();
        super._pause();
    }

    /**
        @dev Triggers unpaused state. Returns functionality for certain functions. Only Governor can call this function.
    */
    function unpause() external {
        _isValidGovernorOrAdmin();
        super._unpause();
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidGovernor() internal view {
        require(msg.sender == globals.governor(), "PF:INVALID_GOVERNOR");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidGovernorOrAdmin() internal {
        require(msg.sender == globals.governor() || admins[msg.sender], "PF:UNAUTHORIZED");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _whenProtocolNotPaused() internal {
        require(!globals.protocolPaused(), "PF:PROTOCOL_PAUSED");
    }
}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ILoan.sol";

import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";

/// @title PremiumCalc calculates premium fees on Loans.
contract PremiumCalc {

    using SafeMath for uint256;

    uint8   public constant calcType = 12;      // PREMIUM type
    bytes32 public constant name     = "FLAT";

    uint256 public immutable premiumFee;  // Flat percentage fee (in basis points) of principal to charge as a premium when calling a Loan

    constructor(uint256 _premiumFee) public {
        premiumFee = _premiumFee;
    }

    /**
        @dev    Calculates the premium payment for a Loan, when making a full payment.
        @param  _loan Loan to calculate a premium payment for
        @return [0] = Principal + Interest
                [1] = Principal
                [2] = Interest
    */
    function getPremiumPayment(address _loan) view public returns(uint256, uint256, uint256) {
        ILoan   loan          = ILoan(_loan);
        uint256 principalOwed = loan.principalOwed();
        uint256 interest      = principalOwed.mul(premiumFee).div(10_000);
        return (interest.add(principalOwed), principalOwed, interest);
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/ILoan.sol";

import "lib/openzeppelin-contracts/contracts/math/SafeMath.sol";

/// @title RepaymentCalc calculates payment amounts on Loans.
contract RepaymentCalc {

	using SafeMath for uint256;

    uint8   public constant calcType = 10;               // INTEREST type
    bytes32 public constant name     = "INTEREST_ONLY";  // Calculator

    /**
        @dev    Calculates the next payment for a Loan.
        @param  _loan Loan to calculate a payment for
        @return [0] = Entitiled interest to the next payment, Principal + Interest only when the next payment is last payment of the loan
                [1] = Entitiled principal amount needs to pay in the next payment
                [2] = Entitiled interest amount needs to pay in the next payment
    */
    function getNextPayment(address _loan) view public returns(uint256, uint256, uint256) {

        ILoan loan = ILoan(_loan);

        uint256 principalOwed = loan.principalOwed();

        // Equation = principal * APR * (paymentInterval / year)
        // Principal * APR gives annual interest
        // Multiplying that by (paymentInterval / year) gives portion of annual interest due for each interval
        uint256 interest =
            principalOwed
                .mul(loan.apr())
                .mul(loan.paymentIntervalSeconds())
                .div(10_000)
                .div(365 days);

        if (loan.paymentsRemaining() == 1) {
            return (interest.add(principalOwed), principalOwed, interest);
        } else {
            return (interest, 0, interest);
        }
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./interfaces/IGlobals.sol";
import "./interfaces/IPool.sol";
import "./interfaces/IPoolFactory.sol";

import "./token/StakeLockerFDT.sol";

import "lib/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";
import "lib/openzeppelin-contracts/contracts/utils/Pausable.sol";

/// @title StakeLocker holds custody of stakeAsset tokens for a given Pool and earns revenue from interest.
contract StakeLocker is StakeLockerFDT, Pausable {

    using SafeMathInt    for int256;
    using SignedSafeMath for int256;
    using SafeERC20      for IERC20;

    uint256 constant WAD = 10 ** 18;  // Scaling factor for synthetic float division

    IERC20  public immutable stakeAsset;  // The asset deposited by stakers into this contract, for liquidation during defaults.

    address public immutable liquidityAsset;  // The liquidityAsset for the Pool as well as the dividend token for FDT interest.
    address public immutable pool;            // The parent liquidity pool.

    uint256 public lockupPeriod;  // Number of seconds for which unstaking is not allowed.

    mapping(address => uint256) public stakeDate;        // Map address to effective stake date value
    mapping(address => uint256) public unstakeCooldown;  // Timestamp of when staker called cooldown()
    mapping(address => bool)    public allowed;          // Map address to allowed status

    bool public openToPublic;  // Boolean opening StakeLocker to public for staking BPTs

    event   BalanceUpdated(address stakeLocker, address token, uint256 balance);
    event AllowListUpdated(address staker, bool status);
    event StakeDateUpdated(address staker, uint256 stakeDate);
    event         Cooldown(address indexed staker, uint256 cooldown);
    event            Stake(uint256 amount, address staker);
    event          Unstake(uint256 amount, address staker);
    event StakeLockerOpened();

    constructor(
        address _stakeAsset,
        address _liquidityAsset,
        address _pool
    ) StakeLockerFDT("Maple Stake Locker", "MPLSTAKE", _liquidityAsset) public {
        liquidityAsset = _liquidityAsset;
        stakeAsset     = IERC20(_stakeAsset);
        pool           = _pool;
        lockupPeriod   = 180 days; // TODO: Confirm default
    }

    /*****************/
    /*** Modifiers ***/
    /*****************/

    /**
        @dev canUnstake enables unstaking in the following conditions:
        1. User is not Pool Delegate and the Pool is in Finalized state.
        2. The Pool is in Initialized or Deactivated state.
    */
    modifier canUnstake() {
        require(
            (msg.sender != IPool(pool).poolDelegate() && IPool(pool).isPoolFinalized()) ||
            !IPool(pool).isPoolFinalized(),
            "StakeLocker:ERR_STAKE_LOCKED"
        );
        _;
    }

    /**
        @dev Modifier to check if msg.sender is Governor.
    */
    modifier isGovernor() {
        require(msg.sender == _globals().governor(), "StakeLocker:MSG_SENDER_NOT_GOVERNOR");
        _;
    }

    /**
        @dev Modifier to check if msg.sender is Pool.
    */
    modifier isPool() {
        require(msg.sender == pool, "StakeLocker:MSG_SENDER_NOT_POOL");
        _;
    }

    /**********************/
    /*** Pool Functions ***/
    /**********************/

    /**
        @dev Update user status on the allowlist. Only Pool can call this.
        @param user   The address to set status for
        @param status The status of user on allowlist
    */
    function setAllowlist(address user, bool status) isPool public {
        allowed[user] = status;
        emit AllowListUpdated(user, status);
    }

    /**
        @dev Set StakerLocker public access. Only PoolDelegate can call this function.
    */
    function openStakeLockerToPublic() external {
        _whenProtocolNotPaused();
        _isValidPoolDelegate();
        openToPublic = true;
        emit StakeLockerOpened();
    }

    /**
        @dev Set the lockup period. Only Pool Delegate can call this function.
        @param newLockupPeriod New lockup period used to restrict unstaking.
     */
    function setLockupPeriod(uint256 newLockupPeriod) external {
        _whenProtocolNotPaused();
        _isValidPoolDelegate();
        require(newLockupPeriod <= lockupPeriod, "StakeLocker:INVALID_VALUE");
        lockupPeriod = newLockupPeriod;
    }

    /**
        @dev Transfers amt of stakeAsset to dst.
        @param dst Desintation to transfer stakeAsset to
        @param amt Amount of stakeAsset to transfer
    */
    function pull(address dst, uint256 amt) isPool external {
        stakeAsset.safeTransfer(dst, amt);
    }

    /**
        @dev Updates loss accounting for FDTs after BPTs have been burned. Only Pool can call this function.
        @param bptsBurned Amount of BPTs that have been burned
    */
    function updateLosses(uint256 bptsBurned) isPool external {
        bptLosses = bptLosses.add(bptsBurned);
        updateLossesReceived();
    }

    /************************/
    /*** Staker Functions ***/
    /************************/

    /**
        @dev Deposit amt of stakeAsset, mint FDTs to msg.sender.
        @param amt Amount of stakeAsset (BPTs) to deposit
    */
    function stake(uint256 amt) whenNotPaused external {
        _whenProtocolNotPaused();
        _isAllowed(msg.sender);

        unstakeCooldown[msg.sender] = uint256(0);  // Reset unstakeCooldown if staker had previously intended to unstake

        _updateStakeDate(msg.sender, amt);

        stakeAsset.safeTransferFrom(msg.sender, address(this), amt);
        _mint(msg.sender, amt);

        emit Stake(amt, msg.sender);
        emit Cooldown(msg.sender, uint256(0));
        emit BalanceUpdated(address(this), address(stakeAsset), stakeAsset.balanceOf(address(this)));
    }

    /**
        @dev Updates information used to calculate unstake delay.
        @param who Staker who deposited BPTs
        @param amt Amount of BPTs staker has deposited
    */
    function _updateStakeDate(address who, uint256 amt) internal {
        uint256 prevDate = stakeDate[who];
        uint256 newDate  = block.timestamp;
        if (prevDate == uint256(0)) {
            stakeDate[who] = newDate;
        } else {
            uint256 dTime  = block.timestamp.sub(prevDate);
            newDate        = prevDate.add(dTime.mul(amt).div(balanceOf(who) + amt));  // stakeDate + (now - stakeDate) * (amt / (balance + amt))
            stakeDate[who] = newDate;
        }
        emit StakeDateUpdated(who, newDate);
    }

    /**
        @dev Activates the cooldown period to unstake. It can't be called if the user is not staking.
    **/
    function intendToUnstake() external {
        require(balanceOf(msg.sender) != uint256(0), "StakeLocker:ZERO_BALANCE");
        unstakeCooldown[msg.sender] = block.timestamp;
        emit Cooldown(msg.sender, block.timestamp);
    }

    /**
        @dev Cancels an initiated unstake by resetting unstakeCooldown.
     */
    function cancelUnstake() external {
        require(unstakeCooldown[msg.sender] != uint256(0), "StakeLocker:NOT_UNSTAKING");
        unstakeCooldown[msg.sender] = 0;
        emit Cooldown(msg.sender, uint256(0));
    }

    /**
        @dev Withdraw amt of stakeAsset minus any losses, claim interest, burn FDTs for msg.sender.
        @param amt Amount of stakeAsset (BPTs) to withdraw
    */
    function unstake(uint256 amt) external canUnstake {
        _whenProtocolNotPaused();
        require(isUnstakeAllowed(msg.sender),                               "StakeLocker:OUTSIDE_COOLDOWN");
        require(stakeDate[msg.sender].add(lockupPeriod) <= block.timestamp, "StakeLocker:FUNDS_LOCKED");

        updateFundsReceived();   // Account for any funds transferred into contract since last call
        _burn(msg.sender, amt);  // Burn the corresponding FDT balance.
        withdrawFunds();         // Transfer full entitled liquidityAsset interest

        stakeAsset.safeTransfer(msg.sender, amt.sub(recognizeLosses()));  // Unstake amt minus losses

        emit Unstake(amt, msg.sender);
        emit BalanceUpdated(address(this), address(stakeAsset), stakeAsset.balanceOf(address(this)));
    }

     /**
        @dev Withdraws all available FDT interest earned for a token holder.
    */
    function withdrawFunds() public override {
        _whenProtocolNotPaused();

        uint256 withdrawableFunds = _prepareWithdraw();

        if (withdrawableFunds > uint256(0)) {
            fundsToken.safeTransfer(msg.sender, withdrawableFunds);

            _updateFundsTokenBalance();
        }
    }

    /**
        @dev Transfer StakerLockerFDTs.
        @param from Address sending   StakeLockerFDTs
        @param to   Address receiving StakeLockerFDTs
        @param wad  Amount of FDTs to transfer
    */
    function _transfer(address from, address to, uint256 wad) internal override canUnstake {
        _whenProtocolNotPaused();
        if (!_globals().isExemptFromTransferRestriction(from) && !_globals().isExemptFromTransferRestriction(to)) {
            require(isReceiveAllowed(unstakeCooldown[to]),    "StakeLocker:RECIPIENT_NOT_ALLOWED");  // Recipient must not be currently unstaking
            require(recognizableLossesOf(from) == uint256(0), "StakeLocker:RECOG_LOSSES");           // If a staker has unrecognized losses, they must recognize losses through unstake
            _updateStakeDate(to, wad);                                                               // Update stake date of recipient
        }
        super._transfer(from, to, wad);
    }

    /***********************/
    /*** Admin Functions ***/
    /***********************/

    /**
        @dev Triggers paused state. Halts functionality for certain functions.
    */
    function pause() external {
        _isValidAdminOrPoolDelegate();
        super._pause();
    }

    /**
        @dev Triggers unpaused state. Returns functionality for certain functions.
    */
    function unpause() external {
        _isValidAdminOrPoolDelegate();
        super._unpause();
    }

    /************************/
    /*** Helper Functions ***/
    /************************/

    /**
        @dev View function to indicate if cooldown period has passed for msg.sender and if they are in the unstake window
    */
    function isUnstakeAllowed(address from) public view returns (bool) {
        IGlobals globals = _globals();
        return block.timestamp - (unstakeCooldown[from] + globals.stakerCooldownPeriod()) <= globals.stakerUnstakeWindow();
    }

    /**
        @dev View function to indicate if recipient is allowed to receive a transfer.
        This is only possible if they have zero cooldown or they are past their unstake window.
    */
    function isReceiveAllowed(uint256 unstakeCooldown) public view returns (bool) {
        IGlobals globals = _globals();
        return block.timestamp > unstakeCooldown + globals.stakerCooldownPeriod() + globals.stakerUnstakeWindow();
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidAdminOrPoolDelegate() internal view {
        require(msg.sender == IPool(pool).poolDelegate() || IPool(pool).admins(msg.sender), "StakeLocker:UNAUTHORIZED");
    }

    /**
        @dev Function to determine if msg.sender is eligible to trigger pause/unpause.
    */
    function _isValidPoolDelegate() internal view {
        require(msg.sender == IPool(pool).poolDelegate(), "StakeLocker:UNAUTHORIZED");
    }

    /**
        @dev Internal function to check whether `msg.sender` is allowed to stake.
    */
    function _isAllowed(address user) internal view {
        require(
            openToPublic || allowed[user] || user == IPool(pool).poolDelegate(),
            "StakeLocker:MSG_SENDER_NOT_ALLOWED"
        );
    }

    /**
        @dev Helper function to return interface of MapleGlobals.
    */
    function _globals() internal view returns(IGlobals) {
        return IGlobals(IPoolFactory(IPool(pool).superFactory()).globals());
    }

    /**
        @dev Function to block functionality of functions when protocol is in a paused state.
    */
    function _whenProtocolNotPaused() internal {
        require(!_globals().protocolPaused(), "StakeLocker:PROTOCOL_PAUSED");
    }

}


// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity 0.6.11;

import "./StakeLocker.sol";

/// @title StakeLockerFactory instantiates StakeLockers.
contract StakeLockerFactory {

    mapping(address => address) public owner;     // owner[locker] = Owner of the stake locker.
    mapping(address => bool)    public isLocker;  // True if stake locker was created by this factory, otherwise false.

    uint8 public constant factoryType = 4;  // i.e FactoryType::STAKE_LOCKER_FACTORY.

    event StakeLockerCreated(
        address owner,
        address stakeLocker,
        address stakeAsset,
        address liquidityAsset,
        string name,
        string symbol
    );

    /**
        @dev Instantiate a StakeLocker contract.
        @param stakeAsset     Address of the stakeAsset (generally Balancer Pool BPTs)
        @param liquidityAsset Address of the liquidityAsset (as defined in the pool)
        @return Address of the instantiated StakeLocker
    */
    function newLocker(
        address stakeAsset,
        address liquidityAsset
    ) external returns (address) {
        address stakeLocker   = address(new StakeLocker(stakeAsset, liquidityAsset, msg.sender));
        owner[stakeLocker]    = msg.sender;
        isLocker[stakeLocker] = true;

        emit StakeLockerCreated(
            msg.sender,
            stakeLocker,
            stakeAsset,
            liquidityAsset,
            StakeLocker(stakeLocker).name(),
            StakeLocker(stakeLocker).symbol()
        );
        return stakeLocker;
    }
}
