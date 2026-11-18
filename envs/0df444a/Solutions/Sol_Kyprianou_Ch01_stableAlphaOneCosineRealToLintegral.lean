-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineRealToLintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:37:11.40273+00:00
-- url     : https://prove2.me/submissions/ab797fe1-7d6c-4f87-8ec3-df4ecb817f4d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosinePositiveIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! Exact original-typed nonnegative integral conversion. -/
theorem solution :
    (∫ x in Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) =
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)).toReal := by
  have hi := Kyprianou.Ch01.stableAlphaOneCosinePositiveIntegrable
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => (1 - Real.cos x) / x ^ 2) := by
    filter_upwards [] with x
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x)
  exact integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable
