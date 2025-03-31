/**
 
*/

// SPDX-License-Identifier: MIT
pragma solidity 0.8.19;

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

interface IUniswapV2Factory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB)
        external
        view
        returns (address pair);

    function allPairs(uint256) external view returns (address pair);

    function allPairsLength() external view returns (uint256);

    function createPair(address tokenA, address tokenB)
        external
        returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;
}

interface IUniswapV2Pair {
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
    event Transfer(address indexed from, address indexed to, uint256 value);

    function name() external pure returns (string memory);

    function symbol() external pure returns (string memory);

    function decimals() external pure returns (uint8);

    function totalSupply() external view returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 value) external returns (bool);

    function transfer(address to, uint256 value) external returns (bool);

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);

    function PERMIT_TYPEHASH() external pure returns (bytes32);

    function nonces(address owner) external view returns (uint256);

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint256);

    function factory() external view returns (address);

    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves()
        external
        view
        returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );

    function price0CumulativeLast() external view returns (uint256);

    function price1CumulativeLast() external view returns (uint256);

    function kLast() external view returns (uint256);

    function mint(address to) external returns (uint256 liquidity);

    function burn(address to)
        external
        returns (uint256 amount0, uint256 amount1);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;

    function skim(address to) external;

    function sync() external;

    function initialize(address, address) external;
}

interface IUniswapV2Router02 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (
            uint256 amountToken,
            uint256 amountETH,
            uint256 liquidity
        );

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    function renounceOwnership() external virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) internal _allowances;
    uint256 private _totalSupply;
    string private _name;
    string private _symbol;

    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    function name() public view virtual override returns (string memory) {
        return _name;
    }

    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    function decimals() public view virtual override returns (uint8) {
        return 9;
    }

    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(address account)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _balances[account];
    }

    function transfer(address recipient, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        unchecked {
            _approve(sender, _msgSender(), currentAllowance - amount);
        }

        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue)
        public
        virtual
        returns (bool)
    {
        _approve(
            _msgSender(),
            spender,
            _allowances[_msgSender()][spender] + addedValue
        );
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue)
        public
        virtual
        returns (bool)
    {
        uint256 currentAllowance = _allowances[_msgSender()][spender];
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        unchecked {
            _approve(_msgSender(), spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        unchecked {
            _balances[sender] = senderBalance - amount;
        }
        _balances[recipient] += amount;

        emit Transfer(sender, recipient, amount);
    }

    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
    }

    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");
        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }
}

contract Token is ERC20, Ownable {
    address public uniswapV2Pair;
    IUniswapV2Router02 public uniswapV2Router;

    struct Taxation {
        Tax pBuy;
        Tax cBuy;
        Tax pSell;
        Tax cSell;
    }

    struct Tax {
        uint256 lp;
        uint256 rfi;
        uint256 marketing;
        uint256 operations;
        uint256 treasury;
    }

    struct Receivers {
        address marketing;
        address operations;
        address treasury;
    }

    struct Proportionalities {
        Ratios buy;
        Ratios sell;
    }

    struct Ratios {
        uint256 lp;
        uint256 marketing;
        uint256 operations;
        uint256 treasury;
    }

    struct Temp {
        uint256 rAmount;
        uint256 rTransferAmount;
        uint256 rFee;
        uint256 tTransferAmount;
        uint256 tReflectionFees;
        uint256 tNonReflectionFees;
    }

    struct Reflection {
        uint256 max;
        uint256 rTotal;
        uint256 tTotal;
        uint256 tFeeTotal;
    }

    struct Limits {
        uint256 buy;
        uint256 sell;
        uint256 fees;
        uint256 wallet;
        bool isEnabled;
    }

    struct Swap {
        bool isEnabled;
        bool isPending;
    }

    mapping(address => uint256) public _rOwned;
    mapping(address => uint256) public _tOwned;

    mapping(address => bool) private _isPair;
    mapping(address => bool) private _isExcludedFromLimits;
    mapping(address => bool) private _isExcludedFromFees;
    mapping(address => bool) private _isExcluded;
    address[] private _excluded;

    Swap public swap;
    Limits public limits;
    Taxation public taxation;
    Receivers public receivers;
    Reflection public reflection;
    Proportionalities public proportionalities;
    bool public isTradingEnabled;

    event SwapEnabled(bool isEnabled);
    event TradingEnabled(bool isEnabled);
    event SwapLimitsEnabled(bool isEnabled);
    event ExcludedFromNonReflectionFees(address account, bool isExcluded);
    event ExcludedFromReflectionFees(address account, bool isExcluded);
    event ExcludedFromSwapLimits(address account, bool isExcluded);
    event ForeignTokensRecovered(uint256 timestamp);
    event OwnerForcedSwapBack(uint256 timestamp);

    event LimitsUpdatedForSwap(
        uint256 buy,
        uint256 sell,
        uint256 fees,
        uint256 wallet
    );
    event TaxUpdatedForSell(
        uint256 lp,
        uint256 rfi,
        uint256 marketing,
        uint256 operations,
        uint256 treasury
    );
    event TaxUpdatedForBuy(
        uint256 lp,
        uint256 rfi,
        uint256 marketing,
        uint256 operations,
        uint256 treasury
    );
    event ReceiversUpdatedForTax(
        address marketing, 
        address operations, 
        address treasury
    );

    receive() external payable {}

    /**
     * @dev Constructor function to initialize the Token contract with initial settings.
     */
    constructor(uint256 supply_) ERC20("BUY AT YOUR OWN RISK", "RISK") {

        // Initialize router and create pair
        uniswapV2Router = IUniswapV2Router02(
            0x10ED43C718714eb63d5aA57B78B54704E256024E
        );
        uniswapV2Pair = IUniswapV2Factory(uniswapV2Router.factory()).createPair(
            address(this),
            uniswapV2Router.WETH()
        );
        

        // Set reflection details
        reflection.max = ~uint256(0);
        reflection.tTotal = supply_ * 10**9;
        reflection.rTotal = (reflection.max - (reflection.max % reflection.tTotal));
        reflection.tFeeTotal;

        // Calculate common limit values
        uint256 commonLimit = reflection.tTotal / 1e2;
        uint256 feeLimit = reflection.tTotal / 1e3;

        // Set limits
        limits.buy = commonLimit;
        limits.sell = commonLimit;
        limits.wallet = commonLimit;
        limits.fees = feeLimit;

        // Set initial tax receivers
        receivers.marketing = msg.sender;
        receivers.operations = msg.sender;
        receivers.treasury = msg.sender;

        // Mark pair as a pair
        _isPair[uniswapV2Pair] = true;
        exclude(uniswapV2Pair);

        // Exclude certain addresses from limits
        _isExcludedFromLimits[msg.sender] = true;
        _isExcludedFromLimits[address(this)] = true;

        // Exclude certain addresses from reflection fees
        _isExcludedFromFees[msg.sender];
        _isExcludedFromFees[address(this)];

        _rOwned[msg.sender] = reflection.rTotal;
        emit Transfer(address(0), msg.sender, reflection.tTotal);
    }

    /**
     * @notice Sets the tax structure for buy transactions.
     * @dev Updates tax values and calculates proportional 
     *      distribution of non-reflection fees.
     * @param lp Liquidity pool fee.
     * @param rfi Reflection fee.
     * @param operations Operations fee.
     * @param marketing Marketing fee.
     * @param treasury Buyback fee.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setTaxForBuy(
        uint256 lp,
        uint256 rfi,
        uint256 operations,
        uint256 marketing,
        uint256 treasury
    ) external onlyOwner {
        uint256 nonReflectionTaxation = lp + operations + marketing + treasury;

        // Store tax values in a single struct assignment
        taxation.cBuy = Tax(lp, rfi, operations, marketing, treasury);

        if (nonReflectionTaxation > 0) {
            proportionalities.buy.lp = (lp * 100) / nonReflectionTaxation;
            proportionalities.buy.operations = (operations * 100) / nonReflectionTaxation;
            proportionalities.buy.marketing = (marketing * 100) / nonReflectionTaxation;
            proportionalities.buy.treasury = (treasury * 100) / nonReflectionTaxation;
        } else {
            // Avoid division by zero, set proportions to zero
            proportionalities.buy.lp = 0;
            proportionalities.buy.operations = 0;
            proportionalities.buy.marketing = 0;
            proportionalities.buy.treasury = 0;
        }

        emit TaxUpdatedForBuy(lp, rfi, operations, marketing, treasury);
    }

    /**
     * @notice Sets the tax structure for sell transactions.
     * @dev Updates tax values and calculates proportional 
     *      distribution of non-reflection fees.
     * @param lp Liquidity pool fee.
     * @param rfi Reflection fee.
     * @param operations Operations fee.
     * @param marketing Marketing fee.
     * @param treasury Byback fee.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setTaxForSell(
        uint256 lp,
        uint256 rfi,
        uint256 operations,
        uint256 marketing,
        uint256 treasury
    ) external onlyOwner {
        uint256 nonReflectionTaxation = lp + operations + marketing + treasury;

        // Store tax values in a single struct assignment
        taxation.cSell = Tax(lp, rfi, operations, marketing, treasury);

        if (nonReflectionTaxation > 0) {
            proportionalities.sell.lp = (lp * 100) / nonReflectionTaxation;
            proportionalities.sell.operations = (operations * 100) / nonReflectionTaxation;
            proportionalities.sell.marketing = (marketing * 100) / nonReflectionTaxation;
            proportionalities.sell.treasury = (treasury * 100) / nonReflectionTaxation;
        } else {
            // Avoid division by zero, set proportions to zero
            proportionalities.sell.lp = 0;
            proportionalities.sell.operations = 0;
            proportionalities.sell.marketing = 0;
            proportionalities.sell.treasury = 0;
        }

        emit TaxUpdatedForSell(lp, rfi, operations, marketing, treasury);
    }

    /**
     * @notice Sets the swap limits.
     * @dev Updates the maximum allowed amounts for 
     *      buy, sell, fees before swap, and wallet.
     * @param buy Maximum amount for buy.
     * @param sell Maximum amount for sell.
     * @param fees Maximum amount before swap fees.
     * @param wallet Maximum amount for wallet.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setSwapLimits(
        uint256 buy,
        uint256 sell,
        uint256 fees,
        uint256 wallet
    ) external onlyOwner {
        // Assign values in a single struct update
        limits = Limits(buy, sell, fees, wallet, limits.isEnabled);

        emit LimitsUpdatedForSwap(buy, sell, fees, wallet);
    }

    /**
     * @notice Sets the tax receiver addresses.
     * @dev Updates the addresses that receive tax 
     *      allocations for marketing and operations.
     * @param marketing Address for marketing tax allocation.
     * @param operations Address for operations tax allocation.
     * @param treasury Address for buyback tax allocation.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setTaxReceivers(address marketing, address operations, address treasury) 
        external 
        onlyOwner 
    {
        // Assign addresses in a single struct update
        receivers = Receivers(payable(marketing), payable(operations), payable(treasury));
        emit ReceiversUpdatedForTax(marketing, operations, treasury);
    }

    /**
     * @notice Enables or disables trading.
     * @dev Updates the trading status.
     * @param isEnabled True to enable trading, false to disable.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setTradingEnabled(bool isEnabled) external onlyOwner {
        isTradingEnabled = isEnabled;
        emit TradingEnabled(isEnabled);
    }

    /**
     * @notice Enables or disables token swapping.
     * @dev Updates the swap functionality status.
     * @param isEnabled True to enable swapping, false to disable.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setSwapEnabled(bool isEnabled) external onlyOwner {
        swap.isEnabled = isEnabled;
        emit SwapEnabled(isEnabled);
    }

    /**
     * @notice Enables or disables swap limits.
     * @dev Updates the swap limit enforcement status.
     * @param isEnabled True to enforce swap limits, false to disable.
     *
     * Requirements:
     * - Can only be called by the owner.
     */
    function setSwapLimitsEnabled(bool isEnabled) external onlyOwner {
        limits.isEnabled = isEnabled;
        emit SwapLimitsEnabled(isEnabled);
    }

    /**
     * @notice Sets the status of an account as a pair.
     * @dev Marks the account as a trading pair or not, and updates reflection status accordingly.
     * @param account The address to be set as a pair or not.
     * @param isPair True to set the account as a pair, false otherwise.
     *
     * Requirements:
     * - Can only be called by the owner.
     * - The account cannot be the initial Uniswap V2 pair.
     */
    function setPair(address account, bool isPair) public onlyOwner {
        _isPair[account] = isPair;

        // Exclude or include account from reflection based on isPair status
        isPair
            ? exclude(account)
            : include(account);
    }

    /**
    * @notice Excludes an account from swap limits.
    * @dev Marks the account as excluded from the swap limits.
    * @param account The address to be excluded from swap limits.
    *
    * Requirements:
    * - Can only be called by the owner.
    * - The account must not already be excluded from swap limits.
    */
    function setExcludedFromSwapLimits(address account, bool isExcluded) public onlyOwner {
        require(!_isExcludedFromLimits[account], "Token: account is already excluded from swap limits");

        // Mark the account as excluded from swap limits
        _isExcludedFromLimits[account] = isExcluded;

        // Emit event for exclusion
        emit ExcludedFromSwapLimits(account, isExcluded);
    }

    /**
     * @notice Update state an account related to non reflection fees.
     * @dev Marks the account as excluded from non reflection fees.
     * @param account The address to be excluded from non reflection fees.
     * @param isExcludedFromNonReflectionFees The state of the account.
     *
     * Requirements:
     * - Can only be called by the owner.
     * - The account cannot be the Uniswap V2 Router.
     * - The account must not already be excluded.
     */
    function setExcludedFromFees(address account, bool isExcludedFromNonReflectionFees) public onlyOwner {
        _isExcludedFromFees[account] = isExcludedFromNonReflectionFees;
        emit ExcludedFromNonReflectionFees(account, isExcludedFromNonReflectionFees);
    }

    /**
     * @notice Excludes an account from reflection fees.
     * @dev Marks the account as excluded from receiving reflection rewards.
     * @param account The address to be excluded from reflection.
     *
     * Requirements:
     * - Can only be called by the owner.
     * - The account cannot be the Uniswap V2 Router.
     * - The account must not already be excluded.
     */
    function exclude(address account) public onlyOwner {
        require(account != address(uniswapV2Router), "Token: must not exclude router");
        require(!_isExcluded[account], "Token: account is already excluded");

        if (_rOwned[account] > 0) {
            _tOwned[account] = reflections(_rOwned[account]);
        } 

        _isExcluded[account] = true;
        _excluded.push(account);
        emit ExcludedFromReflectionFees(account, false);
    }

    /**
     * @notice Includes an account for reflection fees.
     * @dev Marks the account as included for receiving reflection rewards.
     * @param account The address to be included in reflection.
     *
     * Requirements:
     * - Can only be called by the owner.
     * - The account must be excluded from reflection.
     */
    function include(address account) public onlyOwner {
        require(_isExcluded[account], "Token: account is not excluded");

        // Remove the account from the exclusion list by swapping with the last element
        uint256 excludedLength = _excluded.length;
        for (uint256 i = 0; i < excludedLength; i++) {
            if (_excluded[i] == account) {
                // Swap the account with the last one
                _excluded[i] = _excluded[excludedLength - 1];
                _excluded.pop(); // Maintain array integrity
                // Reset the token balance tracking
                _tOwned[account] = 0;
                // Mark the account as included
                _isExcludedFromFees[account] = false;
                break;
            }
        }
        emit ExcludedFromReflectionFees(account, true);
    }

    /**
     * @notice Returns the balance of an account, considering reflection exclusions.
     * @dev If the account is excluded from reflection fees, it returns the custom balance,
     *      otherwise, it returns the calculated reflection balance.
     * @param account The address to query the balance of.
     * @return The balance of the account.
     */
    function balanceOf(address account) public view override returns (uint256) {
        if (_isExcluded[account]) {
            return _tOwned[account];
        }

        // Return the reflection balance for non-excluded accounts
        return reflections(_rOwned[account]);
    }

    /**
     * @notice Returns the total supply of tokens.
     * @dev Retrieves the total token supply from the reflections structure.
     * @return The total supply of tokens.
     */
    function totalSupply() public view override returns (uint256) {
        return reflection.tTotal;
    }

    /**
     * @notice Transfers tokens to a specified address.
     * @dev Executes the transfer by calling the internal `_transfer` function.
     * @param recipient The address to which tokens are being sent.
     * @param amount The amount of tokens to be transferred.
     * @return True if the transfer was successful.
     *
     * Requirements:
     * - The sender must have a sufficient balance.
     * - The transfer must pass all tokenomics and fee calculations.
     */
    function transfer(address recipient, uint256 amount)
        public
        override
        returns (bool)
    {
        _transfer(msg.sender, recipient, amount);
        return true;
    }

    /**
     * @notice Calculates the reflected amount after considering fees.
     * @dev Determines the reflected value based on whether fees are deducted and if it is a buy transaction.
     * @param tAmount The amount of tokens to reflect.
     * @param isFeeDeducted A flag indicating whether fees have been deducted.
     * @param isBuy A flag indicating whether the transaction is a buy.
     * @return The reflected amount based on the provided conditions.
     *
     * Requirements:
     * - `tAmount` must be less than or equal to the total supply.
     */
    function reflected(
        uint256 tAmount,
        bool isFeeDeducted,
        bool isBuy
    ) public view returns (uint256) {
        require(
            tAmount <= reflection.tTotal,
            "Token: amount must be less than supply"
        );

        // Get the transfer values struct
        Temp memory values = _getValues(tAmount, isBuy);

        // Return the reflected amount based on whether fees are deducted
        return isFeeDeducted ? values.rTransferAmount : values.rAmount;
    }

    /**
     * @notice Converts a reflected amount to the equivalent token amount.
     * @dev Uses the rate to calculate the token amount from reflections.
     * @param rAmount The reflected amount to convert.
     * @return The token amount corresponding to the provided reflected amount.
     *
     * Requirements:
     * - `rAmount` must be less than or equal to the total reflected supply.
     */
    function reflections(uint256 rAmount) public view returns (uint256) {
        require(
            rAmount <= reflection.rTotal,
            "Token: amount must be less than total reflections"
        );

        return rAmount / _getRate();
    }

    /**
     * @notice Delivers tokens for reflection (i.e., collects fees).
     * @dev Subtracts the reflected amount from the sender's reflected balance and updates the total reflection supply.
     * @param tAmount The amount of tokens to deliver for reflection.
     * @param isBuy A flag indicating whether the transaction is a buy.
     *
     * Requirements:
     * - The sender must not be excluded from reflection fees.
     * - This function modifies the total reflected supply and fee accumulation.
     */
    function deliver(uint256 tAmount, bool isBuy) public {
        address sender = msg.sender; // Get the sender (the caller of the function)

        // Ensure the sender is not excluded from reflection fees
        require(
            !_isExcluded[sender],
            "Excluded addresses cannot call this function"
        );

        // Get the transfer values including reflection data
        Temp memory values = _getValues(tAmount, isBuy);

        // Subtract the reflected amount from the sender's reflected balance
        _rOwned[sender] = _rOwned[sender] - values.rAmount;

        // Decrease the total reflected supply
        reflection.rTotal = reflection.rTotal - values.rAmount;

        // Increase the total fee accumulation (total tokens reflected as fees)
        reflection.tFeeTotal = reflection.tFeeTotal + tAmount;

        // Emit the Transfer event indicating tokens were sent to the contract (for reflection)
        emit Transfer(sender, address(this), tAmount);
    }

    /**
     * @notice Internal function to transfer tokens between sender and recipient.
     * @dev This function ensures that all the necessary checks and conditions are met before performing a transfer, 
     * including checking for trading enabled status, limits, swap conditions, and reflection fees.
     * @param sender The address from which tokens are sent.
     * @param recipient The address to which tokens are sent.
     * @param amount The amount of tokens to transfer.
     *
     * Requirements:
     * - Sender and recipient cannot be the zero address.
     * - Amount must be greater than zero.
     * - Trading must be enabled unless one of the addresses is excluded from limits.
     * - Buy and sell limits are enforced if enabled, and the sender/recipient are not the owner.
     * - Swap conditions are checked, and the contract will attempt a swap if certain conditions are met.
     * - Fees are applied unless the sender or recipient is excluded from reflection fees.
     */
    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal override {
        // Ensure the sender and recipient are not the zero address
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        // Ensure the transfer amount is greater than zero
        require(amount > 0, "Token: transfer amount must be greater than zero");

        // Determine if this is a buy or sell transaction
        bool isBuy = _isPair[sender];   // If the sender is a pair, it's a buy  
        bool isSell = _isPair[recipient]; // If the recipient is a pair, it's a sell

        // If trading is not enabled, ensure that one of the addresses is excluded from limits
        if (!isTradingEnabled) {
            require(
                _isExcludedFromLimits[sender] ||
                    _isExcludedFromLimits[recipient],
                "Token: trading is disabled"
            );
        }

        // Enforce buy and sell limits if limits are enabled and neither the sender nor recipient is the owner
        if (limits.isEnabled && sender != owner() && recipient != owner()) {
            if (isBuy) {
                require(amount <= limits.buy, "Token: exceeds buy limit");
            } else if (isSell) {
                require(amount <= limits.sell, "Token: exceeds sell limit");
            }
        }

        // Get the contract's token balance
        uint256 contractTokenBalance = balanceOf(address(this));

        // Check if the contract balance meets the minimum required for a swap (if swap is enabled)
        bool overMinTokenBalance = contractTokenBalance >= limits.fees;

        // Trigger a swap if conditions are met (sufficient token balance, and swap is enabled)
        if (
            swap.isEnabled && 
            !swap.isPending && 
            overMinTokenBalance && 
            isSell 
        ) {
            swap.isPending = true; // Flag that swap is in progress
            _swapBack(); // Perform the token swap
            swap.isPending = false; // Reset swap flag
        }

        // Assume that fees should be taken by default
        bool isTaxable = true;

        // If the sender or recipient is excluded from reflection fees, no fees will be applied
        if (
            _isExcludedFromFees[sender] ||
            _isExcludedFromFees[recipient]
        ) {
            isTaxable = false;
        }

        // Perform the token transfer, applying fees if necessary
        _tokenTransfer(sender, recipient, amount, isTaxable, isBuy);
    }

    /**
     * @notice Swaps tokens for ETH using the Uniswap router.
     * @dev This function performs a token swap for ETH by interacting with the UniswapV2Router contract.
     * @param amount The amount of tokens to swap for ETH.
     *
     * Requirements:
     * - The contract must have enough tokens for the swap.
     * - The UniswapV2Router contract must be approved to spend the contract's tokens.
     * - The swap will be executed using the WETH token as the intermediary.
     */
    function _swapTokensForETH(uint256 amount) private {
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniswapV2Router.WETH();

        // Approve the UniswapV2Router contract to spend tokens
        _approve(address(this), address(uniswapV2Router), amount);

        // Execute the swap and send the ETH to the contract
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            amount,
            0, // Accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    /**
     * @notice Executes the swap-back mechanism: swaps tokens for ETH, adds liquidity to Uniswap, 
     * and sends ETH to marketing and operations addresses.
     * @dev This function is responsible for swapping tokens for ETH, adding liquidity, 
     * and distributing the resulting ETH to marketing and operations wallets.
     * @dev It calculates the amount of tokens to swap for ETH, ensures liquidity is added, 
     * and allocates ETH to the marketing and operations addresses.
     * 
     * Requirements:
     * - Contract must have tokens for liquidity and swapping.
     * - Liquidity portion is capped and swapped for ETH.
     * - ETH is distributed based on proportionality settings for marketing and operations.
     */
    function _swapBack() private {
        uint256 contractBalance = balanceOf(address(this));

        // If the contract has no tokens, do nothing
        if (contractBalance == 0) return;

        // Cap the accumulated tokens for swapping to a maximum limit
        if (contractBalance > limits.fees * 20) {
            contractBalance = limits.fees * 20;
        }

        // Determine token allocation for liquidity
        uint256 tokensForLiquidity = (contractBalance *
            proportionalities.sell.lp) / 100;
        uint256 halfLiquidity = tokensForLiquidity / 2;

        // Remaining tokens to swap
        uint256 tokensToSwap = contractBalance - halfLiquidity;
        
        // Swap all tokens except liquidity portion
        _swapTokensForETH(tokensToSwap);
        
        // Get the ETH balance after swap
        uint256 swappedETH = address(this).balance;

        // Calculate ETH needed for liquidity
        uint256 ethForLiquidity = (swappedETH * halfLiquidity) / tokensToSwap;

        // Add liquidity to the pool if conditions are met
        if (halfLiquidity > 0 && ethForLiquidity > 0) {
            addLiquidity(halfLiquidity, ethForLiquidity);
        }

        // Remaining ETH after liquidity is added
        uint256 remainingETH = address(this).balance;

        uint256 totalProportional = 
        proportionalities.sell.marketing + 
        proportionalities.sell.operations + 
        proportionalities.sell.treasury;

        // Transfer ETH to marketing wallet
        uint256 ethForMarketing = (
            remainingETH * 
            proportionalities.sell.marketing) / 
            totalProportional;

        _transferETH(
            receivers.marketing,
            ethForMarketing,
            "Token: transfer to marketing failed"
        );

        // Transfer ETH to operations wallet
        uint256 ethForOperations = (
            remainingETH * proportionalities.sell.operations) / 
            totalProportional;
            
        _transferETH(
            receivers.operations,
            ethForOperations,
            "Token: transfer to operations failed"
        );

        // Transfer remaining ETH to treasury wallet
        _transferETH(
            receivers.treasury,
            address(this).balance,
            "Token: transfer to treasury failed"
        );
    }

    /**
     * @notice Private helper function to transfer ETH to a specified recipient.
     * @dev This function handles the ETH transfer to a recipient address, ensuring success.
     * @param recipient The address to receive the ETH.
     * @param amount The amount of ETH to transfer.
     * @param errorMessage The error message to revert with in case of failure.
     * 
     * Requirements:
     * - The recipient must be a valid address.
     * - The contract must have enough ETH to perform the transfer.
     */
    function _transferETH(
        address recipient,
        uint256 amount,
        string memory errorMessage
    ) private {
        bool success;
        (success, ) = payable(recipient).call{value: amount}("");
        require(success, errorMessage);
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        // approve token transfer to cover all possible scenarios
        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // add the liquidity
        uniswapV2Router.addLiquidityETH{value: ethAmount}(
            address(this),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            owner(),
            block.timestamp
        );
    }

    /**
     * @notice Temporarily removes the swap fees for buy or sell transactions.
     * @dev This function sets the current tax fees for liquidity, reflection, marketing, and operations to zero, 
     * ensuring no fees are taken for the transaction.
     * @param isBuy A boolean indicating whether the transaction is a buy or sell.
     *
     * Requirements:
     * - Taxation structures must be defined for buys and sells.
     * - The tax fees must be reset to zero to temporarily disable them.
     */
    function _removeSwapFee(bool isBuy) private {
        // Select the appropriate tax structures based on buy or sell transaction
        Tax storage previousTax;
        Tax storage currentTax;

        if (isBuy) {
            // Set the buy taxes
            previousTax = taxation.pBuy;
            currentTax = taxation.cBuy;
        } else {
            // Set the sell taxes
            previousTax = taxation.pSell;
            currentTax = taxation.cSell;
        }

        // If no fees are set, exit early to avoid unnecessary operations
        if (
            currentTax.lp == 0 &&
            currentTax.rfi == 0 &&
            currentTax.marketing == 0 &&
            currentTax.operations == 0
        ) {
            return;
        }

        // Save the current fee structure as previous for later restoration
        previousTax.lp = currentTax.lp;
        previousTax.rfi = currentTax.rfi;
        previousTax.marketing = currentTax.marketing;
        previousTax.operations = currentTax.operations;
        previousTax.treasury = currentTax.treasury;

        // Reset the current tax values to zero for the transaction
        currentTax.lp = 0;
        currentTax.rfi = 0;
        currentTax.marketing = 0;
        currentTax.operations = 0;
        currentTax.treasury = 0;
    }

    /**
     * @notice Restores the previous swap fees for buy or sell transactions.
     * @dev This function restores the tax fees for liquidity, reflection, marketing, and operations to their previous values 
     * after being temporarily removed.
     * @param isBuy A boolean indicating whether the transaction is a buy or sell.
     *
     * Requirements:
     * - Taxation structures must be defined for buys and sells.
     * - The previous tax fees must be restored to the current tax fees.
     */
    function _restoreSwapFee(bool isBuy) private {
        // Select the appropriate tax structures based on buy or sell transaction
        Tax storage previousTax;
        Tax storage currentTax;

        if (isBuy) {
            // Use the previous buy tax for purchases
            previousTax = taxation.pBuy;
            currentTax = taxation.cBuy;
        } else {
            // Use the previous sell tax for sales
            previousTax = taxation.pSell;
            currentTax = taxation.cSell;
        }

        // Restore the previous tax values to the current ones
        currentTax.lp = previousTax.lp;
        currentTax.rfi = previousTax.rfi;
        currentTax.marketing = previousTax.marketing;
        currentTax.operations = previousTax.operations;
        currentTax.treasury = previousTax.treasury;
    }

    /**
     * @notice Handles the token transfer logic, accounting for reflection exclusions and fee settings.
     * @dev This function manages the transfer flow depending on whether the sender and recipient 
     * are excluded from reflection fees and whether the transfer is taxable.
     * @param sender The address transferring the tokens.
     * @param recipient The address receiving the tokens.
     * @param amount The amount of tokens to transfer.
     * @param isTaxable A boolean indicating whether the transaction should be taxed.
     * @param isBuy A boolean indicating whether the transaction is a buy (true) or not (false).
     * 
     * Requirements:
     * - Reflection fee exclusion is determined per address.
     * - The transfer flow is determined based on whether fees are applied or not.
     */
    function _tokenTransfer(
        address sender,
        address recipient,
        uint256 amount,
        bool isTaxable,
        bool isBuy
    ) private {
        // Temporarily remove swap fees if the transaction is non-taxable
        if (!isTaxable) _removeSwapFee(isBuy);

        // Determine the correct transfer method based on reflection exclusions
        if (
            _isExcluded[sender] &&
            !_isExcluded[recipient]
        ) {
            // Transfer from excluded address to non-excluded address
            _transferFromExcluded(sender, recipient, amount, isBuy);
        } else if (
            !_isExcluded[sender] &&
            _isExcluded[recipient]
        ) {
            // Transfer to excluded address from non-excluded address
            _transferToExcluded(sender, recipient, amount, isBuy);
        } else if (
            !_isExcluded[sender] &&
            !_isExcluded[recipient]
        ) {
            // Standard transfer without reflection exclusions
            _transferStandard(sender, recipient, amount, isBuy);
        } else if (
            _isExcluded[sender] &&
            _isExcluded[recipient]
        ) {
            // Transfer between two excluded addresses
            _transferBothExcluded(sender, recipient, amount, isBuy);
        } else {
            // Fallback for standard transfer
            _transferStandard(sender, recipient, amount, isBuy);
        }

        // Restore fees if they were temporarily removed
        if (!isTaxable) _restoreSwapFee(isBuy);
    }

    /**
     * @notice Transfers tokens between sender and recipient, applying reflection and fees for standard transfers.
     * @dev This function processes the standard transfer logic, adjusting both the reflected and actual token balances.
     * @param sender The address transferring tokens.
     * @param recipient The address receiving tokens.
     * @param tAmount The amount of tokens to transfer.
     * @param isBuy A boolean indicating whether the transaction is a buy.
     * 
     * Requirements:
     * - Fees are processed according to the current tax structure.
     */
    function _transferStandard(
        address sender,
        address recipient,
        uint256 tAmount,
        bool isBuy
    ) private {
        // Get transfer values using the new struct
        Temp memory values = _getValues(tAmount, isBuy);

        // Prevent underflows
        require(_rOwned[sender] >= values.rAmount, "Token: insufficient rOwned balance");

        // Deduct reflected amount from sender
        _rOwned[sender] -= values.rAmount;

        // Prevent overflow before updating recipient balance
        require(_rOwned[recipient] + values.rTransferAmount >= _rOwned[recipient], "Token: rOwned overflow");

        // Add reflected transfer amount to recipient
        _rOwned[recipient] += values.rTransferAmount;

        // Process non-reflection and reflection fees
        _nonReflectionFees(values.tNonReflectionFees);
        _reflectionFees(values.rFee, values.tReflectionFees);

        // Emit the transfer event
        emit Transfer(sender, recipient, values.tTransferAmount);
    }

    /**
     * @notice Transfers tokens from a sender to an excluded recipient, applying reflection and fees.
     * @dev This function handles the logic when the recipient is excluded from reflections but the sender is not.
     * @param sender The address transferring tokens.
     * @param recipient The address receiving tokens (excluded from reflections).
     * @param tAmount The amount of tokens to transfer.
     * @param isBuy A boolean indicating whether the transaction is a buy.
     * 
     * Requirements:
     * - Reflection for the sender is applied, but the recipient is excluded.
     */
    function _transferToExcluded(
        address sender,
        address recipient,
        uint256 tAmount,
        bool isBuy
    ) private {
        // Get transfer values using the new struct
        Temp memory values = _getValues(tAmount, isBuy);

        // Prevent underflows
        require(_rOwned[sender] >= values.rAmount, "Token: insufficient rOwned balance");

        // Deduct reflected amount from sender
        _rOwned[sender] -= values.rAmount;

        // Prevent overflow before updating recipient balances
        require(_tOwned[recipient] + values.tTransferAmount >= _tOwned[recipient], "Token: tOwned overflow");
        require(_rOwned[recipient] + values.rTransferAmount >= _rOwned[recipient], "Token: rOwned overflow");

        // Add exact token amount to recipient (excluded from reflections)
        _tOwned[recipient] += values.tTransferAmount;
        _rOwned[recipient] += values.rTransferAmount;

        // Process non-reflection and reflection fees
        _nonReflectionFees(values.tNonReflectionFees);
        _reflectionFees(values.rFee, values.tReflectionFees);

        // Emit the transfer event
        emit Transfer(sender, recipient, values.tTransferAmount);
    }

    /**
     * @notice Transfers tokens from an excluded sender to a recipient, applying reflection and fees.
     * @dev This function handles the logic when the sender is excluded from reflections but the recipient is not.
     * @param sender The address transferring tokens (excluded from reflections).
     * @param recipient The address receiving tokens.
     * @param tAmount The amount of tokens to transfer.
     * @param isBuy A boolean indicating whether the transaction is a buy.
     * 
     * Requirements:
     * - Reflection for the recipient is applied, but the sender is excluded.
     */
    function _transferBothExcluded(
        address sender,
        address recipient,
        uint256 tAmount,
        bool isBuy
    ) private {
        // Get transfer values using the new struct
        Temp memory values = _getValues(tAmount, isBuy);

        // Prevent underflows
        require(_tOwned[sender] >= tAmount, "Token: insufficient tOwned balance");
        require(_rOwned[sender] >= values.rAmount, "Token: insufficient rOwned balance");

        // Deduct exact token amount from sender
        _tOwned[sender] -= tAmount;
        _rOwned[sender] -= values.rAmount;

        // Prevent overflow before updating recipient balances
        require(_tOwned[recipient] + values.tTransferAmount >= _tOwned[recipient], "Token: tOwned overflow");
        require(_rOwned[recipient] + values.rTransferAmount >= _rOwned[recipient], "Token: rOwned overflow");

        // Add exact token amount to recipient
        _tOwned[recipient] += values.tTransferAmount;
        _rOwned[recipient] += values.rTransferAmount;

        // Emit the transfer event
        emit Transfer(sender, recipient, values.tTransferAmount);
    }

    /**
     * @notice Transfers tokens between two excluded addresses, applying reflection and fees.
     * @dev This function handles the logic when both the sender and recipient are excluded from reflections.
     * @param sender The address transferring tokens (excluded from reflections).
     * @param recipient The address receiving tokens (excluded from reflections).
     * @param tAmount The amount of tokens to transfer.
     * @param isBuy A boolean indicating whether the transaction is a buy.
     * 
     * Requirements:
     * - Both sender and recipient are excluded from reflections, so only token balances are adjusted.
     */
    function _transferFromExcluded(
        address sender,
        address recipient,
        uint256 tAmount,
        bool isBuy
    ) private {
        // Get transfer values using the new struct
        Temp memory values = _getValues(tAmount, isBuy);

        // Prevent underflows
        require(_tOwned[sender] >= tAmount, "Token: insufficient tOwned balance");
        require(_rOwned[sender] >= values.rAmount, "Token: insufficient rOwned balance");

        // Deduct exact token amount from sender (excluded from reflections)
        _tOwned[sender] -= tAmount;
        _rOwned[sender] -= values.rAmount;

        // Prevent overflow before updating recipient balance
        require(_rOwned[recipient] + values.rTransferAmount >= _rOwned[recipient], "Token: rOwned overflow");

        // Add reflected transfer amount to recipient
        _rOwned[recipient] += values.rTransferAmount;

        // Process non-reflection and reflection fees
        _nonReflectionFees(values.tNonReflectionFees);
        _reflectionFees(values.rFee, values.tReflectionFees);

        // Emit the transfer event
        emit Transfer(sender, recipient, values.tTransferAmount);
    }

    /**
     * @notice Updates the non-reflection fees and their reflected equivalent.
     * @dev Updates the reflected balance for the contract and token balance if excluded from reflections.
     * @param nonReflectionFees The amount of non-reflection fees.
     */
    function _nonReflectionFees(uint256 nonReflectionFees) private {
        // Cache the rate once to avoid redundant calls to _getRate
        uint256 currentRate = _getRate();
        
        // Convert the team tokens to their reflected equivalent
        uint256 rTeam = nonReflectionFees * currentRate;

        // Update the reflected balance for the contract 
        _rOwned[address(this)] += rTeam;

        // Only update if the contract is excluded from reflections 
        if (_isExcluded[address(this)]) {
            _tOwned[address(this)] += nonReflectionFees;
        }
    }

    /**
     * @notice Processes reflection fees by deducting the reflected fee from total supply.
     * @param rFee The reflected fee amount.
     * @param tFee The token fee amount.
     */
    function _reflectionFees(uint256 rFee, uint256 tFee) private {
        // Deduct the reflected fee from the total reflected supply
        reflection.rTotal -= rFee;

        // Add the token fee to the total fee collected
        reflection.tFeeTotal += tFee;
    }

    /**
     * @notice Calculates the values required for a transfer, including reflection and non-reflection fees.
     * @param tAmount The token amount to transfer.
     * @param isBuy Whether the transaction is a buy or sell.
     * @return The TransferValues struct containing all the calculated values.
     */
    function _getValues(uint256 tAmount, bool isBuy)
        private
        view
        returns (Temp memory)
    {
        uint256 reflectionFees;
        uint256 nonReflectionFees;

        // Determine which fee structure to use based on the transaction type (buy/sell)
        if (isBuy) {
            reflectionFees = taxation.cBuy.rfi;
            nonReflectionFees =
                taxation.cBuy.lp +
                taxation.cBuy.marketing +
                taxation.cBuy.operations +
                taxation.cBuy.treasury;
        } else {
            reflectionFees = taxation.cSell.rfi; 
            nonReflectionFees =
                taxation.cSell.lp +
                taxation.cSell.marketing +
                taxation.cSell.operations +
                taxation.cSell.treasury;
        }

        // Calculate token-level transfer values
        (
            uint256 tTransferAmount,
            uint256 tReflectionFees,
            uint256 tNonReflectionFees
        ) = _getTValues(tAmount, reflectionFees, nonReflectionFees);

        // Cache the rate to avoid redundant calls to _getRate
        uint256 currentRate = _getRate();

        // Calculate the reflected values based on the current rate
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee) = _getRValues(
            tAmount,
            tReflectionFees,
            tNonReflectionFees,
            currentRate
        );

        // Return the struct with all the calculated values
        return Temp({
            rAmount: rAmount,
            rTransferAmount: rTransferAmount,
            rFee: rFee,
            tTransferAmount: tTransferAmount,
            tReflectionFees: tReflectionFees,
            tNonReflectionFees: tNonReflectionFees
        });
    }

    /**
    * @notice Calculates the token transfer values including reflection and non-reflection fees.
    * @param tAmount The total amount of tokens to be transferred.
    * @param reflectionFees The percentage of reflection fees to apply.
    * @param nonReflectionFees The total non-reflection fees to apply.
    * @return tTransferAmount The transfer amount after deducting reflection and non-reflection fees.
    * @return tReflectionFees The calculated reflection fees based on the given percentage.
    * @return tNonReflectionFees The calculated non-reflection fees based on the given percentage.
    */
    function _getTValues(
        uint256 tAmount,
        uint256 reflectionFees,
        uint256 nonReflectionFees
    )
        private
        pure
        returns (
            uint256 tTransferAmount,
            uint256 tReflectionFees,
            uint256 tNonReflectionFees
        )
    {
        // Calculate the reflection and non-reflection fees directly
        tReflectionFees = (tAmount * reflectionFees) / 100;
        tNonReflectionFees = (tAmount * nonReflectionFees) / 100;

        // Deduct the fees from the total amount
        tTransferAmount = tAmount - tReflectionFees - tNonReflectionFees;

        return (tTransferAmount, tReflectionFees, tNonReflectionFees);
    }

    /**
    * @notice Calculates the reflected transfer values using the current rate.
    * @param tAmount The token amount to transfer.
    * @param reflectionFees The reflection fee in percentage.
    * @param nonReflectionFees The non-reflection fees in percentage.
    * @param currentRate The current reflection rate (reflected supply / total supply).
    * @return rAmount The total reflected amount based on the token amount and current rate.
    * @return rTransferAmount The transfer amount after deducting reflection and non-reflection fees.
    * @return rReflectionFees The total reflected reflection fee amount.
    */
    function _getRValues(
        uint256 tAmount,
        uint256 reflectionFees,
        uint256 nonReflectionFees,
        uint256 currentRate
    )
        private
        pure
        returns (
            uint256 rAmount,
            uint256 rTransferAmount,
            uint256 rReflectionFees
        )
    {
        // Use the current rate to calculate the reflected values
        rAmount = tAmount * currentRate;
        rReflectionFees = reflectionFees * currentRate;
        uint256 rNonReflectionFees = nonReflectionFees * currentRate;

        // Deduct the fees from the total reflected amount
        rTransferAmount = rAmount - rReflectionFees - rNonReflectionFees;

        return (rAmount, rTransferAmount, rReflectionFees);
    }

    /**
     * @notice Returns the current reflection rate based on the total supply.
     * @dev This rate is used for converting token amounts to their reflected equivalents.
     * @return The current reflection rate (reflected supply / total supply).
     */
    function _getRate() public view returns (uint256) {
        // Cache the current supply to avoid multiple calls to _getCurrentSupply()
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();

        // Return the reflection rate
        return rSupply / tSupply;
    }

    /**
     * @notice Returns the current reflected and token supply, adjusted for excluded addresses.
     * @return rSupply The current reflected supply.
     * @return tSupply The current token supply.
     */
    function _getCurrentSupply() private view returns (uint256 rSupply, uint256 tSupply) {
        rSupply = reflection.rTotal;
        tSupply = reflection.tTotal;

        // Cache the length of the excluded list
        uint256 excludedLength = _excluded.length;

        for (uint256 i = 0; i < excludedLength; i++) {
            uint256 rOwnedExcluded = _rOwned[_excluded[i]];
            uint256 tOwnedExcluded = _tOwned[_excluded[i]];

            // If an excluded address holds more tokens than the total supply,
            // prevent underflow and return the original total supply.
            if (rOwnedExcluded > rSupply || tOwnedExcluded > tSupply) {
                return (reflection.rTotal, reflection.tTotal);
            }

            // Adjust the total supply by excluding the balances of excluded addresses
            unchecked {
                rSupply -= rOwnedExcluded;
                tSupply -= tOwnedExcluded;
            }
        }

        // Ensure we don't return a reflection supply that's too low
        if (rSupply < reflection.rTotal / reflection.tTotal) {
            return (reflection.rTotal, reflection.tTotal);
        }

        return (rSupply, tSupply);
    }

    function transferForeignToken(address _token, address _to)
        external
        onlyOwner
        returns (bool _sent)
    {
        require(_token != address(0), "_token address cannot be 0");
        require(_token != address(this), "Can't withdraw native tokens");
        uint256 _contractBalance = IERC20(_token).balanceOf(address(this));
        _sent = IERC20(_token).transfer(_to, _contractBalance);
        emit ForeignTokensRecovered(block.timestamp);
    }

    // force Swap back if slippage issues.
    function forceSwapBack() external onlyOwner {
        require(
            balanceOf(address(this)) >= limits.fees,
            "Can only swap when token amount is at or higher than restriction"
        );
        swap.isPending = true; // Flag that swap is in progress
        _swapBack(); // Perform the token swap
        swap.isPending = false; // Reset swap flag  
        emit OwnerForcedSwapBack(block.timestamp);
    }    

}