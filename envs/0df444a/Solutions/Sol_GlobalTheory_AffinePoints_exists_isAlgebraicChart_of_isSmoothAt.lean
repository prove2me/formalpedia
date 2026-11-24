-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_isSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:48.056259+00:00
-- url     : https://prove2.me/submissions/c9b34c50-51a6-4869-80af-b80dca88f38c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_notMem_isStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_isAlgebraicChart_of_away


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
theorem _root_.solution [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) (p : A →ₐ[ℂ] ℂ)
    (hp : haveI := RingHom.ker_isPrime p; Algebra.IsSmoothAt ℂ (RingHom.ker p)) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e ∧ p ∈ e.source := by
  haveI := RingHom.ker_isPrime p
  obtain ⟨s, hs, H⟩ := exists_notMem_isStandardSmoothOfRelativeDimension (K := ℂ) hd
    (RingHom.ker p)
  exact exists_isAlgebraicChart_of_away s (Localization.Away s) p hs
end GlobalTheory.AffinePoints
