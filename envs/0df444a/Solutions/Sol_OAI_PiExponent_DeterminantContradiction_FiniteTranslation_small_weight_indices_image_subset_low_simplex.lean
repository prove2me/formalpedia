-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:12:04.573644+00:00
-- url     : https://prove2.me/submissions/b36e7ef7-4f9f-477f-ab33-e9eef2b01cca

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_realWeightedSimplex_mem_of_pos_weighted_sum_le
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_finite_logWeights_pos

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Finset.univ.filter
      (fun a : Index d H => weight d a ≤ (d.base.A : ℝ) * H)).image
        (fun a => a.1) ⊆
      realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H) := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact realWeightedSimplex_mem_of_pos_weighted_sum_le
    (a := a.1)
    (hT := mul_pos (show 0 < (d.base.A : ℝ) by
      exact d.base.theta_pos.trans d.base.theta_lt_A) hH)
    (hw := fun i => finite_logWeights_pos d i)
    (ha := by simpa [weight] using (Finset.mem_filter.mp ha).2)