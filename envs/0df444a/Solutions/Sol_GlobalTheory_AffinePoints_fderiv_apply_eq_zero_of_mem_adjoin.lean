-- Prove2me | solution 1 for GlobalTheory.AffinePoints.fderiv_apply_eq_zero_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:35.217939+00:00
-- url     : https://prove2.me/submissions/0ab38248-883b-4cb0-a5cf-f7c89ab3ddc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_mul
import Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_add

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
theorem _root_.solution {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E) {s : Set A}
    (hs : ∀ a ∈ s, fderiv ℂ (fun z => φ z a) z v = 0) {a : A} (ha : a ∈ Algebra.adjoin ℂ s) :
    fderiv ℂ (fun z => φ z a) z v = 0 := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hs a ha
  | algebraMap c => simp
  | add a b _ _ ha hb => rw [fderiv_apply_add hφ, ha, hb, add_zero]
  | mul a b _ _ ha hb => rw [fderiv_apply_mul hφ, ha, hb]; simp
end GlobalTheory.AffinePoints
