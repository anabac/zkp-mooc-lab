pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;

    // var m = 1 << b;
    // component less_than = LessThan(252);
    // less_than.in[0] <== in;
    // less_than.in[1] <== m;
    // out <== less_than.out;

    signal rem <-- (1 << b) - (in % (1 << b));
    // rem > 0
    component rem_gt0 = LessThan(b);
    rem_gt0.in <== [0, rem];
    // in + rem == 2**b
    component sum_eq_2b = IsEqual();
    sum_eq_2b.in <== [in + rem, 1 << b];
    out <== sum_eq_2b.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);
    signal input x;
    signal output y;

    component x_bit_length = CheckBitLength(b);
    x_bit_length.in <== x;
    x_bit_length.out === 1;

    y <-- x >> shift;
    component bit_length = CheckBitLength(shift);
    bit_length.in <== x - y * (1 << shift);
    bit_length.out === 1;

    // component x_n2b = Num2Bits(b);
    // x_n2b.in <== x;
    // component y_b2n = Bits2Num(shift);
    // for (var i = 0; i < b-shift; i++) {
    //     y_b2n.bits[i] <== x_n2b.bits[shift+i];
    // }
    // y <== y_b2n.out;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    // skip_checks is either 1 or 0
    skip_checks * (1 - skip_checks) === 0;

    component equals_shift[shift_bound];
    var bounded_shift = 0;

    signal shifted1 <-- (1 << shift) * (1-skip_checks);
    var two_pow_shift = 0;
    
    // bounded_shift = 1 iff 0 <= shift < shift_bound
    for (var i = 0; i < shift_bound; i++) {
        equals_shift[i] = IsEqual();
        equals_shift[i].in <== [shift, i];
        bounded_shift += equals_shift[i].out;

        two_pow_shift += equals_shift[i].out * (1 << i);
    }
    // if skip_checks == 0 then 0 <= shift < shift_bound
    (1 - skip_checks) * (1 - bounded_shift) === 0;
    // if skip_checks == 0 then shifted1 == two_pow_shift else shifted1 == 0
    shifted1 === two_pow_shift * (1-skip_checks);
    
    y <== x * shifted1;

}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // skip_checks is either 1 or 0
    skip_checks * (1 - skip_checks) === 0;
    // in != 0
    component is_in_0 = IsZero();
    is_in_0.in <== in;
    is_in_0.out * (1 - skip_checks) === 0;

    component in_n2b = Num2Bits(b);
    in_n2b.in <== in;

    var sum_bits = 0;
    component msnzb_not_found[b];
    for (var i = b-1; i >= 0; i--) {
        one_hot[i] <== (1 - sum_bits) * in_n2b.bits[i];
        
        msnzb_not_found[i] = OR();
        msnzb_not_found[i].a <== sum_bits;
        msnzb_not_found[i].b <== in_n2b.bits[i];
        sum_bits = msnzb_not_found[i].out;
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // m != 0
    component is_m_0 = IsZero();
    is_m_0.in <== m;
    is_m_0.out * (1 - skip_checks) === 0;

    component ell = MSNZB(P+1);
    ell.in <== m;
    ell.skip_checks <== skip_checks;
    component two_pow_ell_b2n = Bits2Num(P+1);
    two_pow_ell_b2n.bits <== ell.one_hot;

    // m <<= (P - ell)
    signal inv <-- skip_checks ? 0 : 1/two_pow_ell_b2n.out;
    inv * two_pow_ell_b2n.out === 1 - skip_checks;
    m_out <== m * (1 << P) * inv;

    // e = e + ell - p
    var ell_num = 0;
    for (var i = 0; i < P+1; i++) {
        ell_num += i * ell.one_hot[i];
    }
    e_out <== e + ell_num - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // Well-formedness
    component check_well_formed_0 = CheckWellFormedness(k, p);
    check_well_formed_0.e <== e[0];
    check_well_formed_0.m <== m[0];
    component check_well_formed_1 = CheckWellFormedness(k, p);
    check_well_formed_1.e <== e[1];
    check_well_formed_1.m <== m[1];

    // Magnitude comparison
    var mgn_1 = e[0] * (1 << (p+1)) + m[0];
    var mgn_2 = e[1] * (1 << (p+1)) + m[1];
    component mgn_compare = LessThan(k+p+1);
    mgn_compare.in <== [mgn_1, mgn_2];

    component switch_e = Switcher();
    switch_e.sel <== mgn_compare.out;
    switch_e.L <== e[0];
    switch_e.R <== e[1];
    var alpha_e = switch_e.outL;
    var beta_e = switch_e.outR;

    component switch_m = Switcher();
    switch_m.sel <== mgn_compare.out;
    switch_m.L <== m[0];
    switch_m.R <== m[1];
    var alpha_m = switch_m.outL;
    var beta_m = switch_m.outR;

    var diff = alpha_e - beta_e;
    // or_condition = diff > p + 1 or alpha_e == 0
    component pplus1_lt_diff = LessThan(k);
    pplus1_lt_diff.in <== [p+1, diff];
    component is_alpha_e_zero = IsZero();
    is_alpha_e_zero.in <== alpha_e;
    component or_condition = OR();
    or_condition.a <== pplus1_lt_diff.out;
    or_condition.b <== is_alpha_e_zero.out;
    component if_e = IfThenElse();
    if_e.cond <== or_condition.out;
    component if_m = IfThenElse();
    if_m.cond <== or_condition.out;
    // if or_condition:
    if_e.L <== alpha_e;
    if_m.L <== alpha_m;
    // else:
    // alpha_m <<= diff
    component alpha_m_lshift = LeftShift(1 << k);
    alpha_m_lshift.x <== alpha_m;
    alpha_m_lshift.shift <== diff;
    alpha_m_lshift.skip_checks <== or_condition.out;
    alpha_m = alpha_m_lshift.y;

    component normalized = Normalize(k, p, 2*p+1);
    normalized.m <== alpha_m + beta_m;
    normalized.e <== beta_e;
    normalized.skip_checks <== or_condition.out;

    component round_check = RoundAndCheck(k, p, 2*p+1);
    round_check.e <== normalized.e_out;
    round_check.m <== normalized.m_out;

    if_e.R <== round_check.e_out;
    if_m.R <== round_check.m_out;

    // return
    e_out <== if_e.out;
    m_out <== if_m.out;
}
