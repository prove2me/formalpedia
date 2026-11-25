-- Prove2me | solution 1 for GlobalTheory.AffinePoints.rank_le_of_immersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:48.407204+00:00
-- url     : https://prove2.me/submissions/a9145bd8-86f8-4a23-a352-84d099707425

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_finite_injective_of_ringKrullDim_eq
import Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_eq_zero_of_mem_adjoin
import Theorems.Thm_GlobalTheory_AffinePoints_exists_isOpen_fderiv_eq_zero

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
theorem _root_.solution [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hU : IsOpen U) (hne : U.Nonempty) (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U)
    (himm : ∀ z ∈ U, ∀ v, (∀ a, fderiv ℂ (fun z => φ z a) z v = 0) → v = 0) :
    Module.rank ℂ E ≤ d := by
  classical
  obtain ⟨g, -, hg⟩ := exists_finite_injective_of_ringKrullDim_eq (K := ℂ) hd
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hg
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ A).out
  have key : ∀ t : Finset A, ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, ∀ v,
      (∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) →
        ∀ a ∈ t, fderiv ℂ (fun z => φ z a) z v = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨U, subset_rfl, hU, hne, by simp⟩
    | insert a t _ ih =>
      obtain ⟨V, hVU, hV, hVne, H⟩ := ih
      obtain ⟨W, hWV, hW, hWne, H'⟩ := exists_isOpen_fderiv_eq_zero (φ := φ) g.toRingHom (hint a)
        hV hVne fun a => (hφ a).mono hVU
      refine ⟨W, hWV.trans hVU, hW, hWne, fun z hz v hv b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact H' z hz v hv
      · exact H z (hWV hz) v hv b hb
  obtain ⟨V, hVU, -, ⟨z, hz⟩, H⟩ := key s
  have hd' : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z := fun a =>
    (hφ a).differentiableAt (hU.mem_nhds (hVU hz))
  let L : E →ₗ[ℂ] (Fin d → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun z => φ z (g (X i))) z : E →ₗ[ℂ] ℂ)
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine himm z (hVU hz) v fun a => fderiv_apply_eq_zero_of_mem_adjoin hd' v
      (H z hz v fun r => ?_) (hs ▸ Algebra.mem_top)
    refine fderiv_apply_eq_zero_of_mem_adjoin hd' v (s := range fun i => g (X i)) ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact congrFun hv i
    · rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨r, (DFunLike.congr_fun (MvPolynomial.aeval_unique g) r).symm⟩
  simpa using L.lift_rank_le_of_injective hL
end GlobalTheory.AffinePoints
