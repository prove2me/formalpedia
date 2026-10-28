-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center_multiplier_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:08:21.358732+00:00
-- url     : https://prove2.me/submissions/0ec51573-d2a0-49c7-8084-c82041c20567

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) (i : Fin d.m)
    (k : ℕ) (hk : k ≤ d.K) :
    ‖(k : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by
  obtain ⟨hq2, -, happ⟩ := d.approximations i.val
  set q : ℕ := d.q i.val with hqdef
  set p : ℤ := d.p i.val with hpdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  -- the complex number
  have hc : MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period
      = (2 * Complex.I) * (((p : ℝ) / q - Real.pi : ℝ) : ℂ) := by
    simp only [MatrixArithmetic.rationalCenters, finiteNumerators, finiteDenominators, period]
    push_cast
    rw [← hpdef, ← hqdef]
    ring
  have hnorm : ‖(k : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)‖
      = 2 * k * |Real.pi - (p : ℝ) / q| := by
    rw [hc, norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast, norm_mul,
      Complex.norm_I, Complex.norm_two, Real.norm_eq_abs, abs_sub_comm]
    ring
  rw [hnorm]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hfw : fixedWeights d i ≤ Real.log q + 1 := by
    simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators]
    exact (Nat.ceil_lt_add_one hlogq).le
  have hpow : (q : ℝ) ^ (-nu) = Real.exp (-nu * Real.log q) := by
    rw [Real.rpow_def_of_pos hqpos]; ring_nf
  calc 2 * (k : ℝ) * |Real.pi - (p : ℝ) / q| ≤ 2 * d.K * (q : ℝ) ^ (-nu) := by
        apply mul_le_mul _ happ (abs_nonneg _) (by positivity)
        have : (k : ℝ) ≤ d.K := by exact_mod_cast hk
        linarith
    _ = Real.exp (Real.log (2 * (d.K : ℝ)) + (-nu * Real.log q)) := by
        rw [Real.exp_add, Real.exp_log (by positivity), hpow]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith
