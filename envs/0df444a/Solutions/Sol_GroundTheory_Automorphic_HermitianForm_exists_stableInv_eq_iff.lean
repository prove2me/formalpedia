-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_stableInv_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:32.831814+00:00
-- url     : https://prove2.me/submissions/3da43148-cfa6-43b7-8fc8-b0d8ea98d675

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_stableInv_conj
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_inKernel_mk
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_forall_toSesq_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_apply_apply
import Theorems.Thm_GroundTheory_Automorphic_TorusE_ext
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (x : h.centralizerTorusFirstCohomology γ) :
    (∃ γ' ∈ h.unitaryGroup, StablyConjugate (γ : V ≃ₗ[E] V) γ' ∧ h.stableInv γ γ' = x) ↔
      h.InKernel γ x := by
  induction x using QuotientGroup.induction_on with
  | H c =>
  rw [inKernel_mk]
  constructor
  · rintro ⟨_, hU, ⟨g, rfl⟩, hinv⟩
    rw [stableInv_conj _ _ _ hU, invOf] at hinv
    have H0 : Isometric (h.twistOf γ (h.normOf γ g hU)) h :=
      ⟨g, fun x y => by rw [twistOf_apply, val_normOf, toSesq_apply_apply]⟩
    exact (h.twistOf_isometric_of_mk_eq γ hinv).symm.trans H0
  · rintro ⟨e, he⟩
    have hee : h.adjointEquiv e * e = (c : TorusE (γ : V ≃ₗ[E] V)).val :=
      (h.forall_toSesq_eq_iff e _).1 fun x y => (he x y).trans (twistOf_apply _ _ _ _ _)
    have hU : e * γ * e⁻¹ ∈ h.unitaryGroup := by
      rw [h.conj_mem_unitaryGroup_iff γ.2, hee]
      exact (c : TorusE (γ : V ≃ₗ[E] V)).val_mem
    refine ⟨_, hU, ⟨e, rfl⟩, ?_⟩
    rw [stableInv_conj _ _ _ hU, invOf]
    congr 1
    exact Subtype.ext (TorusE.ext hee)
end GroundTheory.Automorphic.HermitianForm
