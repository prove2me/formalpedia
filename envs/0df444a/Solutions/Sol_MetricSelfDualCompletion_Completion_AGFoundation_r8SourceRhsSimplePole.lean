-- Prove2me | solution 1 for MetricSelfDualCompletion.Completion.AGFoundation.r8SourceRhsSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:40:50.540289+00:00
-- url     : https://prove2.me/submissions/d2887d2d-4114-4f75-9673-1376bd4b3793

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace

set_option autoImplicit false
set_option linter.all false

namespace MetricSelfDualCompletion.Completion.AGFoundation

open QEC.Coding.AlgebraicGeometry
open scoped WithZero

/-- The actual r=8 source recursion preserves a normalized simple pole. -/
theorem sourceRhs_pole_contract
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    x ≠ 0 ∧ x ^ 7 + 1 ≠ 0 ∧ x ^ 8 / (x ^ 7 + 1) ≠ 0 ∧
      P.order (x ^ 7 + 1) = -7 ∧
      P.order (x ^ 8 / (x ^ 7 + 1)) = -1 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    simp [GlobalPlace.order] at hx
  have hpow (y : K) (n : ℕ) :
      P.order (y ^ n) = (n : ℤ) * P.order y := by
    unfold GlobalPlace.order
    rw [map_pow, WithZero.log_pow]
    simp only [nsmul_eq_mul]
    ring
  have hvalue (y : K) (hy : y ≠ 0) :
      P.valuation y = WithZero.exp (-P.order y) := by
    unfold GlobalPlace.order
    rw [neg_neg]
    exact (WithZero.exp_log (P.valuation.ne_zero_iff.mpr hy)).symm
  have hxpow0 : x ^ 7 ≠ 0 := pow_ne_zero 7 hx0
  have hxpoworder : P.order (x ^ 7) = -7 := by
    rw [hpow, hx]
    norm_num
  have hxpowvalue : P.valuation (x ^ 7) = WithZero.exp (7 : ℤ) := by
    rw [hvalue (x ^ 7) hxpow0, hxpoworder]
    norm_num
  have hlt : P.valuation 1 < P.valuation (x ^ 7) := by
    rw [map_one, hxpowvalue, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hdenorder : P.order (x ^ 7 + 1) = -7 := by
    unfold GlobalPlace.order
    rw [P.valuation.map_add_eq_of_lt_left hlt, hxpowvalue, WithZero.log_exp]
  have hden0 : x ^ 7 + 1 ≠ 0 := by
    intro hzero
    rw [hzero] at hdenorder
    simp [GlobalPlace.order] at hdenorder
  have hrhs0 : x ^ 8 / (x ^ 7 + 1) ≠ 0 := div_ne_zero (pow_ne_zero 8 hx0) hden0
  have hmul (y z : K) (hy : y ≠ 0) (hz : z ≠ 0) :
      P.order (y * z) = P.order y + P.order z := by
    unfold GlobalPlace.order
    rw [P.valuation.map_mul y z, WithZero.log_mul
      (P.valuation.ne_zero_iff.mpr hy) (P.valuation.ne_zero_iff.mpr hz)]
    ring
  have hinv (y : K) : P.order y⁻¹ = -P.order y := by
    unfold GlobalPlace.order
    rw [(P.valuation).map_inv y, WithZero.log_inv]
  have hrhsorder : P.order (x ^ 8 / (x ^ 7 + 1)) = -1 := by
    rw [div_eq_mul_inv, hmul _ _ (pow_ne_zero 8 hx0) (inv_ne_zero hden0),
      hinv, hpow, hx, hdenorder]
    norm_num
  exact ⟨hx0, hden0, hrhs0, hdenorder, hrhsorder⟩

end MetricSelfDualCompletion.Completion.AGFoundation

#print axioms MetricSelfDualCompletion.Completion.AGFoundation.sourceRhs_pole_contract

theorem solution
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    x ≠ 0 ∧ x ^ 7 + 1 ≠ 0 ∧ x ^ 8 / (x ^ 7 + 1) ≠ 0 ∧
      P.order (x ^ 7 + 1) = -7 ∧
      P.order (x ^ 8 / (x ^ 7 + 1)) = -1 :=
  MetricSelfDualCompletion.Completion.AGFoundation.sourceRhs_pole_contract P x hx

#print axioms solution
