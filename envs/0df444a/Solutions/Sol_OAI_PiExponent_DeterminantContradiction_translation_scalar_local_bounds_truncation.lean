-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_truncation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:47:17.087671+00:00
-- url     : https://prove2.me/submissions/318cad42-b2c5-4815-9b7f-d1653f1e39ac

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    (∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by
  have hw : ∀ i : Fin d.m, 0 < fixedWeights d i := by
    intro i
    simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators]
    have hq : (2 : ℝ) ≤ (d.q i.val : ℝ) := by exact_mod_cast (d.approximations i.val).1
    have hlog : 0 < Real.log (d.q i.val : ℝ) := Real.log_pos (by linarith)
    exact_mod_cast Nat.ceil_pos.mpr hlog
  constructor
  · intro i
    simp only [MatrixArithmetic.truncationOrders]
    apply Nat.one_le_iff_ne_zero.mpr
    apply ne_of_gt
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos d.F0_pos (hw i)) d.v0_pos
  · intro i
    simp only [MatrixArithmetic.truncationOrders]
    have h := Nat.le_ceil (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
    rw [div_le_iff₀ d.v0_pos] at h
    simp only [fixedWeights]
    linarith
