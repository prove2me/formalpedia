-- Prove2me | solution 1 for GlobalTheory.AffinePoints.volume_coords_image_zeroSet_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:42.020185+00:00
-- url     : https://prove2.me/submissions/000c260a-89e9-4da1-b0ce-fde58db60cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_faithfulSMul_and_isAlgebraic_of_etale
import Theorems.Thm_GlobalTheory_AffinePoints_volume_coords_image_zeroSet

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
theorem _root_.solution [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Etale) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) A := hg
  exact volume_coords_image_zeroSet g (faithfulSMul_and_isAlgebraic_of_etale _ A).2 hf
end GlobalTheory.AffinePoints
