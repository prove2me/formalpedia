-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:41:58.145504+00:00
-- url     : https://prove2.me/submissions/5854e798-231e-4241-ac5d-0bcfe10cad78

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L006

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_OscillatorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem sqrtFactorial_pos (n : ℕ) : 0 < sqrtFactorial n := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos n

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SourceIntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_one_sum (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U 1 z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩]
  simp only [Int.natCast_one,one_pow,mul_one]
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter,List.toFinset_range]
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_filter,Finset.mem_range] at hh ⊢
    omega
  · intro h hh hn
    simp only [Finset.mem_range,Finset.mem_filter,decide_eq_true_eq,not_and] at hh hn
    by_cases hhz : h ≤ z
    · have hbound : ¬ p+z ≤ T+h := hn (by omega)
      rw [Nat.choose_eq_zero_of_lt (by omega : T-z < p-h)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : z < h)]
      simp

theorem integerCouplingPolynomial_coeff (z n p : ℕ) (hp : p ≤ z+n) :
    (integerCouplingPolynomial z n).coeff p = U 1 z (z+n) p := by
  rw [U_one_sum z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold integerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  have hpos : (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 := by simp
  rw [hneg,hpos,coeff_X_add_C_pow,coeff_X_add_C_pow]
  simp

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SourceEqualSpinPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem equalSpin_polynomial (u : ℝ) (z n : ℕ) :
    couplingPolynomial u u z n = C (u^(z+n)) *
      (Certificate.integerCouplingPolynomial z n).map (Int.castRingHom ℝ) := by
  simp only [couplingPolynomial,Certificate.integerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,pow_add,C_mul,C_pow]
  rw [show C u * X-C u = C u*(X-1) by ring,
    show C u * X+C u = C u*(X+1) by ring,mul_pow,mul_pow]
  ring

theorem equalSpin_polynomialCoefficient (u : ℝ) (z n p : ℕ) (hp : p ≤ z+n) :
    couplingPolynomialCoefficient u u z n p =
      u^(z+n) * (Certificate.U 1 z (z+n) p : ℝ) *
        sqrtFactorial p * sqrtFactorial (z+n-p) / (sqrtFactorial z * sqrtFactorial n) := by
  unfold couplingPolynomialCoefficient
  rw [equalSpin_polynomial,coeff_C_mul,coeff_map,Certificate.integerCouplingPolynomial_coeff z n p hp]
  simp only [Int.coe_castRingHom,monomialNormFactor]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FactorialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_factorial_coefficient_s50_oai (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) (hr : r ≤ j+k) :
    fourBodyLimitCoefficient r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) * (Certificate.V r D T p j k : ℝ) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  have hi : r+(j+k-r)=j+k := by omega
  have ho : (D-r)+(T-D)=T-r := by omega
  have hk : j+k-j=k := by omega
  have hb : T-r-p=j+k-r := by omega
  rw [fourBodyLimitCoefficient,ite_eq_left hr,
    equalSpin_polynomialCoefficient _ r (j+k-r) j (by omega),
    equalSpin_polynomialCoefficient _ (D-r) (T-D) p (by omega)]
  rw [hi,ho,hk,hb]
  simp only [Certificate.V,ite_eq_left hr,Int.cast_mul]
  rw [pow_add]
  field_simp [ne_of_gt (sqrtFactorial_pos r),ne_of_gt (sqrtFactorial_pos (D-r)),
    ne_of_gt (sqrtFactorial_pos (T-D)),ne_of_gt (sqrtFactorial_pos (j+k-r))]
  ring

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50_oai := @OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50_oai
