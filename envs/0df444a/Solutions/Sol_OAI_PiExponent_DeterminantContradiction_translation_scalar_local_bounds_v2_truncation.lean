-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:37:59.586143+00:00
-- url     : https://prove2.me/submissions/97b419b4-a922-438d-bb56-bb891de9cae7

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    (∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by
  constructor
  · intro i
    have hq : 1 < (finiteDenominators d i : ℝ) := by
      dsimp [finiteDenominators]
      have hq2 := (d.approximations i.val).1
      exact_mod_cast (show 1 < d.q i.val by omega)
    have hlog : 0 < Real.log (finiteDenominators d i : ℝ) := Real.log_pos hq
    change 1 ≤ Nat.ceil (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i /
      (d.v0 : ℝ))
    have hratio : 0 < d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ) := by
      apply div_pos
      · exact mul_pos d.F0_pos (by
          change 0 < (Nat.ceil (Real.log (finiteDenominators d i : ℝ)) : ℝ)
          exact_mod_cast (Nat.ceil_pos.mpr hlog))
      · exact d.v0_pos
    have hp : 0 < Nat.ceil (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ)) :=
      Nat.ceil_pos.mpr hratio
    omega
  · intro i
    have hceil :
        d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i /
          (d.v0 : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) := by
      change _ ≤ (Nat.ceil _ : ℝ)
      exact Nat.le_ceil _
    have hden : 0 < (d.v0 : ℝ) := d.v0_pos
    have hbound := (div_le_iff₀ hden).mp hceil
    simpa [fixedWeights, mul_comm] using hbound