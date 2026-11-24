-- Prove2me | solution 1 for GlobalTheory.AffinePoints.volume_image_eq_zero_of_finrank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:45.047945+00:00
-- url     : https://prove2.me/submissions/cd9b6efa-87b4-49b8-aba7-d5606520166c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_addHaar_image_eq_zero_of_finrank_lt

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
variable {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : finrank ℂ E < d) {s : Set E} {f : E → Fin d → ℂ}
    (hf : DifferentiableOn ℂ f s) : volume (f '' s) = 0 := by
  refine addHaar_image_eq_zero_of_finrank_lt volume ?_ (hf.restrictScalars ℝ)
  rw [finrank_real_of_complex, finrank_real_of_complex]
  simpa using h
end GlobalTheory.AffinePoints
