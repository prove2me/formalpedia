-- Prove2me | solution 1 for GlobalTheory.AffinePoints.surjective_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:05.013923+00:00
-- url     : https://prove2.me/submissions/04ad7c91-1447-4e54-80e4-9bf25c976c5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_surjective_comap_of_isIntegral


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
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (hinj : Function.Injective g) : Function.Surjective (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).surjective.comp
    (surjective_comap_of_isIntegral g (RingHom.Finite.to_isIntegral hg) hinj)
end GlobalTheory.AffinePoints
