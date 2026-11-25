-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.finrank_intertwiners_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:03.86179+00:00
-- url     : https://prove2.me/submissions/c27557f9-6a72-4bf8-9149-b7944dfdb96b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_eq_zero_of_forall_orthogonalProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_summandEquivL_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_summandEquivL_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_sumEquivL_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_comp_sumEquivL
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_eq_zero_of_not_isEquivalent
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_exists_eq_smul_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
variable {σ : UnitaryRep G K}
include hsum hirr
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (hσ : σ.IsIrreducible)
    (hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      Module.finrank ℂ (σ.intertwiners π) = Nat.card (EquivSummands hinv σ) := by
  classical
  have : Finite (EquivSummands hinv σ) := hW.to_subtype
  let _ : Fintype (EquivSummands hinv σ) := Fintype.ofFinite _
  let Ψ : (EquivSummands hinv σ → ℂ) →ₗ[ℂ] σ.intertwiners π :=
    { toFun := fun c => ⟨sumEquivL hinv c, sumEquivL_mem hinv c⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        apply Subtype.ext
        simp [sumEquivL, smul_smul, Finset.smul_sum] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext w
    have h1 : ∀ k, (V w.1).orthogonalProjectionOnto (sumEquivL hinv c k) = 0 := by
      intro k
      have := congrArg (fun T : σ.intertwiners π => (T : K →L[ℂ] H) k) hc
      change sumEquivL hinv c k = 0 at this
      rw [this, map_zero]
    have h2 : c w • summandEquivL hinv w = 0 := by
      ext1 k
      have := h1 k
      rw [orthogonalProjection_comp_sumEquivL hinv hsum, dif_pos w.2] at this
      simpa using this
    have := hσ.1
    obtain ⟨k, hk⟩ := exists_ne (0 : K)
    have h3 := congrArg (fun S : K →L[ℂ] V w.1 => S k) h2
    simp only [smul_apply, zero_apply] at h3
    rcases smul_eq_zero.1 h3 with h | h
    · exact h
    · exfalso
      have h4 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
      rw [h, norm_zero] at h4
      exact hk (norm_eq_zero.1 h4.symm)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨T, hT⟩
    have hPT : ∀ w : EquivSummands hinv σ, ∃ c : ℂ,
        (V w.1).orthogonalProjectionOnto ∘L T = c • summandEquivL hinv w := fun w =>
      hσ.exists_eq_smul_of_mem_intertwiners (hirr w.1) (summandEquivL_mem hinv w)
        (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv w.1) hT)
        (summandEquivL_ne_zero hinv hσ w)
    choose c hc using hPT
    refine ⟨c, Subtype.ext ?_⟩
    change sumEquivL hinv c = T
    ext1 k
    refine (sub_eq_zero.1 (eq_zero_of_forall_orthogonalProjection hsum fun j => ?_)).symm
    rw [map_sub, orthogonalProjection_comp_sumEquivL hinv hsum]
    split_ifs with h
    · have := congrArg (fun S : K →L[ℂ] V j => S k) (hc ⟨j, h⟩)
      simp only [comp_apply, smul_apply] at this
      rw [this, sub_self]
    · have h0 : (V j).orthogonalProjectionOnto ∘L T = 0 :=
        hσ.eq_zero_of_not_isEquivalent (hirr j) (fun e => h e.symm)
          (comp_mem_intertwiners (orthogonalProjection_mem_intertwiners hinv j) hT)
      have := congrArg (fun S : K →L[ℂ] V j => S k) h0
      simp only [comp_apply, zero_apply] at this
      rw [this, sub_zero]
  let e := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.finiteDimensional e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
end GroundTheory.Automorphic.UnitaryRep
