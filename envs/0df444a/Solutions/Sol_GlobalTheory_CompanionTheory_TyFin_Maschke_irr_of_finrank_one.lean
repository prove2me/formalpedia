-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.irr_of_finrank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:44:08.989129+00:00
-- url     : https://prove2.me/submissions/f9f6c54a-a875-4eb0-9616-2a38522faedd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_rep_inv_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_id_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V)
    (h : Module.finrank ℂ (Intw ρ ρ) = 1) : IsIrr ρ := by
  have hV : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have : Subsingleton (Intw ρ ρ) := inferInstance
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, fun S hS => ?_⟩
  obtain ⟨q, hq⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  set p := avg ρ ρ (S.subtype ∘ₗ q) with hp
  have hpS : ∀ v, p v ∈ S := fun v => by
    rw [hp, avg_apply]
    refine S.smul_mem _ (S.sum_mem fun g _ => hS g _ ?_)
    exact (q (ρ g⁻¹ v)).2
  have hq' : ∀ w (hw : w ∈ S), ((q w : S) : V) = w := fun w hw => by
    have := LinearMap.congr_fun hq ⟨w, hw⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfix : ∀ w ∈ S, p w = w := fun w hw => by
    have h1 : ∀ g : Γ, ρ g ((S.subtype ∘ₗ q) (ρ g⁻¹ w)) = w := fun g => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hq' _ (hS _ _ hw), rep_inv_apply]
    rw [hp, avg_apply]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hne : (⟨LinearMap.id, id_mem ρ⟩ : Intw ρ ρ) ≠ 0 := fun h0 => by
    have h1 : (LinearMap.id : V →ₗ[ℂ] V) = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (LinearMap.congr_fun h1 x)
  obtain ⟨c, hcp⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h ⟨p, avg_mem ρ ρ _⟩
  have hpc : ∀ v, p v = c • v := fun v => by
    have h1 : c • (LinearMap.id : V →ₗ[ℂ] V) = p := congrArg Subtype.val hcp
    rw [← h1]; rfl
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot, ← hfix w hw, hpc, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have h1 : v = c⁻¹ • p v := by rw [hpc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1]
    exact S.smul_mem _ (hpS v)
end GlobalTheory.CompanionTheory.TyFin.Maschke
