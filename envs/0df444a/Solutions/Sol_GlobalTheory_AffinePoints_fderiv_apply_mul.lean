-- Prove2me | solution 1 for GlobalTheory.AffinePoints.fderiv_apply_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:46.197747+00:00
-- url     : https://prove2.me/submissions/0aa5ee7f-8afc-413f-9641-2094772eafff

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
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {z : E} (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (a b : A) : fderiv ℂ (fun z => φ z (a * b)) z v =
      φ z a * fderiv ℂ (fun z => φ z b) z v + φ z b * fderiv ℂ (fun z => φ z a) z v := by
  simp only [map_mul]
  rw [fderiv_fun_mul (hφ a) (hφ b)]
  simp
end GlobalTheory.AffinePoints
