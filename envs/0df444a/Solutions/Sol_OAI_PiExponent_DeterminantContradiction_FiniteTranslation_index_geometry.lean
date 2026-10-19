-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:56:37.834359+00:00
-- url     : https://prove2.me/submissions/ab3016bd-73c7-4da1-9fb4-5136825c321a

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_geometry_cardinality
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_selected_weight_dominates_row_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_actual_mean_normalization

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) ∧
      (∀ f : Family d H, (∏ r : Row d H, scalar d r (f r)) ≠ 0 →
        (actualRowCount d H : ℝ) * H * actualMean d H ≤
          ∑ r : Row d H, weight d (f r).1) := by
  obtain ⟨hcount, hweight, hcapacity⟩ :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality d hH
  refine ⟨hcount, hweight, hcapacity, ?_⟩
  intro f hf
  calc
    (actualRowCount d H : ℝ) * H * actualMean d H =
        MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization d hH
    _ ≤ ∑ r : Row d H, weight d (f r).1 :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum d f hf