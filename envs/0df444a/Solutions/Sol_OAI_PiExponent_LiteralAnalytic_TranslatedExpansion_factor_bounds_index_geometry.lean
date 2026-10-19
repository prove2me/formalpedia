-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_index_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T10:04:13.970423+00:00
-- url     : https://prove2.me/submissions/b2ef008d-6c80-4c7a-9da6-7e126fe983a1

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_lowIndexCount_pos
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translatedIndexWeight_nonneg
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_low_transverse_capacity

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
    (∀ a : indices d H, 0 ≤ translatedIndexWeight d a) ∧
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) := by
  exact ⟨lowIndexCount_pos d hH,
    (fun a => translatedIndexWeight_nonneg d a),
    low_transverse_capacity d H⟩