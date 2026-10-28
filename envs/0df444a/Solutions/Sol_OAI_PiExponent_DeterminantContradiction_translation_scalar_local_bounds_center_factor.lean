-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_center_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:48:33.09965+00:00
-- url     : https://prove2.me/submissions/bfe1ce34-bb0f-4ad4-b158-cc5ce6a85b6f

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hlogK : 0 ≤ Real.log (2 * (d.K : ℝ)) := Real.log_nonneg (by linarith)
  refine ⟨by linarith, fun i => ?_⟩
  obtain ⟨hq2, -, happrox⟩ := d.approximations i.val
  set q : ℝ := (d.q i.val : ℝ) with hqdef
  set p : ℝ := (d.p i.val : ℝ) with hpdef
  have hq : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq2
  have hq0 : 0 < q := by linarith
  -- the complex number
  have hc : MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
      period = ((2 * (p / q - Real.pi) : ℝ) : ℂ) * Complex.I := by
    simp only [MatrixArithmetic.rationalCenters, finiteNumerators, finiteDenominators, period, hpdef,
      hqdef]
    push_cast
    field_simp
  rw [hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs, abs_mul, abs_two]
  have hj : (r.1.val : ℝ) ≤ d.K := by exact_mod_cast r.1.isLt.le
  have habs : |p / q - Real.pi| ≤ q ^ (-nu) := by rw [abs_sub_comm]; exact happrox
  -- q^(-nu) = exp(-nu log q) ≤ exp(nu - nu * ceil(log q))
  have hlw : fixedWeights d i ≤ Real.log q + 1 := by
    simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators]
    exact (Nat.ceil_lt_add_one (Real.log_nonneg (by linarith))).le
  have hpow : q ^ (-nu) ≤ Real.exp (nu - nu * fixedWeights d i) := by
    rw [Real.rpow_def_of_pos hq0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp : Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) =
      (2 * d.K) * Real.exp (nu - nu * fixedWeights d i) := by
    rw [show (Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i =
      Real.log (2 * (d.K : ℝ)) + (nu - nu * fixedWeights d i) by ring, Real.exp_add,
      Real.exp_log (by linarith)]
  rw [hexp]
  have h1 : 0 ≤ |p / q - Real.pi| := abs_nonneg _
  have h2 : 0 ≤ (r.1.val : ℝ) := Nat.cast_nonneg _
  calc (r.1.val : ℝ) * (2 * |p / q - Real.pi|) ≤ d.K * (2 * q ^ (-nu)) := by
        apply mul_le_mul hj (by linarith) (by positivity) (by linarith)
    _ ≤ d.K * (2 * Real.exp (nu - nu * fixedWeights d i)) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = (2 * d.K) * Real.exp (nu - nu * fixedWeights d i) := by ring
