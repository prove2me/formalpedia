-- Prove2me | solution 1 for GlobalTheory.AffinePoints.addHaar_image_eq_zero_of_finrank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:35.823959+00:00
-- url     : https://prove2.me/submissions/81602fde-390e-4d93-a73c-eb8df18d5b5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
namespace GlobalTheory.AffinePoints
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (h : finrank ℝ E < finrank ℝ F) {s : Set E} {f : E → F} (hf : DifferentiableOn ℝ f s) :
    μ (f '' s) = 0 := by
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.1 h.le
  obtain ⟨L, hL⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hsurj : Function.Surjective L := fun x => ⟨i x, DFunLike.congr_fun hL x⟩
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  let L' : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  have him : f '' s = (f ∘ L') '' (L' ⁻¹' s) := by
    rw [image_comp, image_preimage_eq s (f := L') hsurj]
  rw [him]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => (fderivWithin ℝ f s (L' x)).comp L') (fun x hx => ?_) (fun x _ => ?_)
  · exact (hf _ hx).hasFDerivWithinAt.comp x L'.hasFDerivWithinAt (mapsTo_preimage _ _)
  · refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 fun h0 => hker (le_bot_iff.1 ?_)
    rw [← h0]
    intro v hv
    have : L' v = 0 := hv
    simp [this]
end GlobalTheory.AffinePoints
