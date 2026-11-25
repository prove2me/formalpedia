-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isProperMap_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:42.027337+00:00
-- url     : https://prove2.me/submissions/fcc4485c-b184-4ec4-9166-833833415f24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_isProperMap_comap


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
theorem _root_.solution (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite) :
    IsProperMap (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph ℂ ℂ (Fin d)).isProperMap.comp
    (isProperMap_comap g (RingHom.Finite.to_isIntegral hg))
end GlobalTheory.AffinePoints
