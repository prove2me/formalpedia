-- Prove2me | solution 1 for N25.unitRelationNumeratorPolynomial25_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:10.520204+00:00
-- url     : https://prove2.me/submissions/9f3ae038-1562-4e31-8bcc-38825db2c618

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate
import Theorems.Thm_Polynomial_abs_coeff_binomial_product_le_exp

set_option autoImplicit false

namespace N25

open Polynomial

private theorem pair_exponent_sum_bound (t a b : ℕ)
    (ha : a ≤ 25) (hb : b ≤ 25) :
    (((unitPairBlocks25 t a b).flatten).map fun e => ((63 : ℝ) / 64) ^ e).sum ≤ 16 := by
  let q : ℝ := 63 / 64
  let r : ℝ := q ^ 25
  have hq₀ : 0 ≤ q := by norm_num [q]
  have hq₁ : q ≤ 1 := by norm_num [q]
  have hr₀ : 0 ≤ r := pow_nonneg hq₀ _
  have hr₁ : r ≤ 3 / 4 := by norm_num [r, q]
  have hgeom (u : ℕ) :
      ((List.range u).map fun m => r ^ m).sum + 4 * r ^ u ≤ 4 := by
    induction u with
    | zero => norm_num
    | succ u ih =>
        simp only [List.range_succ, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton, pow_succ]
        have hrpow := pow_nonneg hr₀ u
        have hmul := mul_le_mul_of_nonneg_left hr₁ hrpow
        calc
          _ ≤ ((List.range u).map fun m => r ^ m).sum + r ^ u +
                4 * (r ^ u * (3/4)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hmul (by norm_num))
          _ = ((List.range u).map fun m => r ^ m).sum + 4 * r ^ u := by ring
          _ ≤ 4 := ih
  have hstream (m c : ℕ) : q ^ (25 * m + c) ≤ r ^ m := by
    rw [pow_add, ← pow_mul]
    exact mul_le_of_le_one_right (pow_nonneg hq₀ (25*m)) (pow_le_one₀ hq₀ hq₁)
  have hpoint (m : ℕ) :
      q ^ (25*m+a) + q ^ (25*m+b) + q ^ (25*(m+1)-a) + q ^ (25*(m+1)-b) ≤
        4 * r ^ m := by
    have hea : 25*(m+1)-a = 25*m+(25-a) := by omega
    have heb : 25*(m+1)-b = 25*m+(25-b) := by omega
    rw [hea, heb]
    linarith [hstream m a, hstream m b, hstream m (25-a), hstream m (25-b)]
  have hlist (l : List ℕ) :
      (l.map fun m =>
        q ^ (25*m+a) + q ^ (25*m+b) + q ^ (25*(m+1)-a) + q ^ (25*(m+1)-b)).sum ≤
        4 * (l.map fun m => r ^ m).sum := by
    induction l with
    | nil => simp
    | cons m l ih =>
        simp only [List.map_cons, List.sum_cons]
        linarith [hpoint m]
  have hsum : ((List.range t).map fun m => r ^ m).sum ≤ 4 := by
    have := hgeom t
    have := pow_nonneg hr₀ t
    linarith
  have hflat :
      (((unitPairBlocks25 t a b).flatten).map fun e => q ^ e).sum =
        ((List.range t).map fun m =>
          q ^ (25*m+a) + q ^ (25*m+b) + q ^ (25*(m+1)-a) + q ^ (25*(m+1)-b)).sum := by
    simp [unitPairBlocks25, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, add_assoc]
  change (((unitPairBlocks25 t a b).flatten).map fun e => q ^ e).sum ≤ 16
  rw [hflat]
  linarith [hlist (List.range t)]

private theorem binomial_flatten (blocks : List (List ℕ)) :
    ((blocks.flatten.map fun e => (1 - X ^ e : ℤ[X])).prod) =
      Polynomial.binomialBlocksPolynomial blocks := by
  simp [Polynomial.binomialBlocksPolynomial, List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def]

private theorem binomial_replicate (es : List ℕ) (k : ℕ) :
    (((List.replicate k es).flatten.map fun e => (1 - X ^ e : ℤ[X])).prod) =
      ((es.map fun e => (1 - X ^ e : ℤ[X])).prod) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, pow_succ, mul_comm]

private theorem exponent_sum_replicate (es : List ℕ) (q : ℝ) (k : ℕ) :
    (((List.replicate k es).flatten.map fun e => q ^ e).sum) =
      (k : ℝ) * (es.map fun e => q ^ e).sum := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, Nat.cast_add, add_mul]; ring

private theorem relation_term_weight_bound (a b c s n : ℕ) (habc : a+b+c = 9) :
    |((X ^ s * (unitPairPolynomial25 199 1 7) ^ a *
      (unitPairPolynomial25 199 3 4) ^ b * (unitPairPolynomial25 199 2 11) ^ c).coeff n : ℝ)| *
        ((63 : ℝ) / 64) ^ n ≤ Real.exp 144 := by
  let ep := (unitPairBlocks25 199 1 7).flatten
  let er := (unitPairBlocks25 199 2 11).flatten
  let es := (unitPairBlocks25 199 3 4).flatten
  let all := (List.replicate a ep).flatten ++ (List.replicate b es).flatten ++
    (List.replicate c er).flatten
  let q : ℝ := 63 / 64
  have hsum : (all.map fun e => q ^ e).sum ≤ 144 := by
    have hp := pair_exponent_sum_bound 199 1 7 (by norm_num) (by norm_num)
    have hr := pair_exponent_sum_bound 199 2 11 (by norm_num) (by norm_num)
    have hs := pair_exponent_sum_bound 199 3 4 (by norm_num) (by norm_num)
    have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) a)
    have hr' := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) c)
    have hs' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) b)
    have habc' : (a : ℝ) + b + c = 9 := by exact_mod_cast habc
    dsimp [all]
    simp only [List.map_append, List.sum_append, exponent_sum_replicate]
    dsimp [ep, er, es, q] at *
    nlinarith
  have h := Polynomial.abs_coeff_binomial_product_le_exp q
    (by norm_num [q]) (by norm_num [q]) all s n
  have heq :
      (all.map fun e => (1 - X ^ e : ℤ[X])).prod =
        unitPairPolynomial25 199 1 7 ^ a * unitPairPolynomial25 199 3 4 ^ b *
          unitPairPolynomial25 199 2 11 ^ c := by
    simp only [all, List.map_append, List.prod_append, binomial_replicate]
    rw [show (ep.map fun e => (1-X^e : ℤ[X])).prod = unitPairPolynomial25 199 1 7 by
          exact binomial_flatten _,
        show (es.map fun e => (1-X^e : ℤ[X])).prod = unitPairPolynomial25 199 3 4 by
          exact binomial_flatten _,
        show (er.map fun e => (1-X^e : ℤ[X])).prod = unitPairPolynomial25 199 2 11 by
          exact binomial_flatten _]
  rw [heq] at h
  simpa only [mul_assoc] using h.trans (Real.exp_le_exp.mpr hsum)

private theorem abs_nine_terms_le (E v0 v1 v2 v3 v4 v5 v6 v7 v8 : ℝ)
    (h0 : |v0| ≤ E)
    (h1 : |v1| ≤ E)
    (h2 : |v2| ≤ E)
    (h3 : |v3| ≤ E)
    (h4 : |v4| ≤ E)
    (h5 : |v5| ≤ E)
    (h6 : |v6| ≤ E)
    (h7 : |v7| ≤ E)
    (h8 : |v8| ≤ E)
    : |v0-v1+v2-v3-2*v4-v5-v6-2*v7+v8| ≤ 11*E := by
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,
    h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

private theorem numerator_weight_bound (p r s : ℤ[X]) (n : ℕ)
    (hb₀ : |((X^8*p^4*s^4*r^1).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₁ : |((X^9*p^6*s^3*r^0).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₂ : |((X^5*p^3*s^2*r^4).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₃ : |((X^7*p^5*s^2*r^2).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₄ : |((X^8*p^6*s^2*r^1).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₅ : |((X^5*p^4*s^1*r^4).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₆ : |((X^6*p^5*s^1*r^3).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₇ : |((X^7*p^6*s^1*r^2).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    (hb₈ : |((X^7*p^7*s^0*r^2).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤ Real.exp 144)
    : |((unitRelationNumerator25 X p r s).coeff n : ℝ)| * ((63 : ℝ)/64)^n ≤
      11 * Real.exp 144 := by
  let q : ℝ := 63/64
  let t₀ : ℤ[X] := X^8*p^4*s^4*r^1
  let t₁ : ℤ[X] := X^9*p^6*s^3*r^0
  let t₂ : ℤ[X] := X^5*p^3*s^2*r^4
  let t₃ : ℤ[X] := X^7*p^5*s^2*r^2
  let t₄ : ℤ[X] := X^8*p^6*s^2*r^1
  let t₅ : ℤ[X] := X^5*p^4*s^1*r^4
  let t₆ : ℤ[X] := X^6*p^5*s^1*r^3
  let t₇ : ℤ[X] := X^7*p^6*s^1*r^2
  let t₈ : ℤ[X] := X^7*p^7*s^0*r^2
  have hqpow : 0 ≤ q ^ n := pow_nonneg (by norm_num [q]) n
  have heq : unitRelationNumerator25 X p r s =
      t₀-t₁+t₂-t₃-C 2*t₄-t₅-t₆-C 2*t₇+t₈ := by
    dsimp [unitRelationNumerator25,
      t₀,t₁,t₂,t₃,t₄,t₅,t₆,t₇,t₈]
    norm_num
    ring
  rw [← abs_of_nonneg hqpow, ← abs_mul]
  have hcoef : ((unitRelationNumerator25 X p r s).coeff n : ℝ) * q^n =
      (t₀.coeff n : ℝ)*q^n-(t₁.coeff n : ℝ)*q^n+(t₂.coeff n : ℝ)*q^n-
      (t₃.coeff n : ℝ)*q^n-2*((t₄.coeff n : ℝ)*q^n)-(t₅.coeff n : ℝ)*q^n-
      (t₆.coeff n : ℝ)*q^n-2*((t₇.coeff n : ℝ)*q^n)+(t₈.coeff n : ℝ)*q^n := by
    rw [heq]
    simp only [coeff_sub, coeff_add, coeff_C_mul]
    push_cast
    ring
  rw [hcoef]
  apply abs_nine_terms_le
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₀
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₁
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₂
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₃
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₄
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₅
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₆
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₇
  · simpa only [abs_mul, abs_of_nonneg hqpow] using hb₈

/-- The low coefficients of the finite level-25 numerator are bounded by two
to the three-hundred-and-sixtieth power. -/
theorem _root_.solution (n : ℕ) (hn : n < 4951) :
    |(unitRelationNumeratorPolynomial25 199).coeff n| < (2 : ℤ) ^ 360 := by
  let q : ℝ := 63 / 64
  have hb₀ := relation_term_weight_bound 4 4 1 8 n (by norm_num)
  have hb₁ := relation_term_weight_bound 6 3 0 9 n (by norm_num)
  have hb₂ := relation_term_weight_bound 3 2 4 5 n (by norm_num)
  have hb₃ := relation_term_weight_bound 5 2 2 7 n (by norm_num)
  have hb₄ := relation_term_weight_bound 6 2 1 8 n (by norm_num)
  have hb₅ := relation_term_weight_bound 4 1 4 5 n (by norm_num)
  have hb₆ := relation_term_weight_bound 5 1 3 6 n (by norm_num)
  have hb₇ := relation_term_weight_bound 6 1 2 7 n (by norm_num)
  have hb₈ := relation_term_weight_bound 7 0 2 7 n (by norm_num)
  have hweighted : |((unitRelationNumeratorPolynomial25 199).coeff n : ℝ)| * q ^ n ≤
      11 * Real.exp 144 :=
    numerator_weight_bound (unitPairPolynomial25 199 1 7)
      (unitPairPolynomial25 199 2 11) (unitPairPolynomial25 199 3 4) n
      hb₀ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇ hb₈
  have hrecip : ((64 : ℝ) / 63) ^ n ≤ Real.exp 79 := by
    have hbase : (64 : ℝ) / 63 ≤ Real.exp (1/63) := by
      linarith [Real.add_one_le_exp ((1 : ℝ)/63)]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64/63) hbase n
    rw [← Real.exp_nat_mul] at hp
    apply hp.trans (Real.exp_le_exp.mpr _)
    have hn' : (n : ℝ) ≤ 4950 := by exact_mod_cast (show n ≤ 4950 by omega)
    nlinarith
  have hreal : |((unitRelationNumeratorPolynomial25 199).coeff n : ℝ)| ≤
      11 * Real.exp 223 := by
    have hident : q ^ n * ((64 : ℝ) / 63) ^ n = 1 := by rw [← mul_pow]; norm_num [q]
    calc
      _ = (|((unitRelationNumeratorPolynomial25 199).coeff n : ℝ)| * q ^ n) *
          ((64 : ℝ)/63)^n := by rw [mul_assoc, hident, mul_one]
      _ ≤ (11 * Real.exp 144) * Real.exp 79 :=
        mul_le_mul hweighted hrecip (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; norm_num
  have hexp : Real.exp 223 ≤ (3 : ℝ)^223 := by
    have h := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) 223
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hfinal : (11 : ℝ) * (3 : ℝ)^223 < (2 : ℝ)^360 := by
    rw [show 360 = 180 * 2 from rfl, pow_mul]
    norm_num
  have htotal : |((unitRelationNumeratorPolynomial25 199).coeff n : ℝ)| < (2 : ℝ)^360 :=
    lt_of_le_of_lt (hreal.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))) hfinal
  rw [show 360 = 180 * 2 from rfl, pow_mul] at htotal ⊢
  exact_mod_cast htotal

end N25
