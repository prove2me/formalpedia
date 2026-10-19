-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:07:43.261104+00:00
-- url     : https://prove2.me/submissions/8a4739a5-a568-4915-8c62-9f87f7ee0dd0

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_low_simplex_nonempty
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_weights_nonneg
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_small_weight_indices_image_subset_low_simplex

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) := by
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.low_simplex_nonempty
      d hH
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_weights_nonneg d
  · classical
    let S : Finset (Index d H) := Finset.univ.filter
      (fun a => weight d a ≤ (d.base.A : ℝ) * H)
    have himage :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
        d hH
    have hcard : (S.image Subtype.val).card = S.card := by
      apply Finset.card_image_iff.mpr
      intro x hx y hy hxy
      exact Subtype.ext hxy
    change (S.card : ℝ) ≤ (lowIndexCount d H : ℝ)
    rw [← hcard]
    change ((S.image Subtype.val).card : ℝ) ≤
      ((realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H)).card : ℝ)
    exact_mod_cast Finset.card_le_card (by simpa [S] using himage)