-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:08:20.192103+00:00
-- url     : https://prove2.me/submissions/0e222cad-1ed1-4f6c-a6df-0237456c515c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv
set_option autoImplicit false
open MeasureTheory
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ((W 0 0 = 0) ↔
        ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure) ∧
      (HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
        0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure ∧
        W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹) := by
  intro Ω mΩ P hP D ψ W hψ hW
  constructor
  · constructor
    · intro hz hbv
      have h := source_result8_6_zero_discount_v3_bv Ω P D ψ W hψ hW hbv
      have hp : 0 < (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹ :=
        inv_pos.mpr h.1
      exact (ne_of_gt hp) (by simpa [h.2] using hz)
    · intro hnbv
      exact source_result8_6_zero_discount_v3_unbounded Ω P D ψ W hψ hW hnbv
  · intro hbv
    exact source_result8_6_zero_discount_v3_bv Ω P D ψ W hψ hW hbv
