-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.low_simplex_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:11:01.317446+00:00
-- url     : https://prove2.me/submissions/0cb9c4e8-90e2-4d7f-900c-87aacbda80ab

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) := by
  classical
  have hA : 0 < (d.base.A : ℝ) := lt_trans d.base.theta_pos d.base.theta_lt_A
  have hcut : 0 ≤ (d.base.A : ℝ) * H := le_of_lt (mul_pos hA hH)
  let z : Fin d.m → ℕ := fun _ => 0
  have hz : z ∈ realWeightedSimplex
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((d.base.A : ℝ) * H) := by
    rw [realWeightedSimplex]
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      simp [z]
    · simpa [z] using hcut
  unfold lowIndexCount
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨z, hz⟩)