-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts_of_simpleIffIrr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:04.86084+00:00
-- url     : https://prove2.me/submissions/0ca80e4f-e126-4960-acb8-a941ec33e043

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_comp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_exists_left_inverse
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_exists_right_inverse
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_injective_of_irr
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_surjective_of_irr
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_irr_of_finrank_one

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
theorem _root_.solution (hs : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr) :
    ReciprocityTheory.Ty.Fin.St.MaschkeFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ V _ _ _ ρ hτ
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    constructor
    · rintro ⟨φ, hφ, h0⟩
      obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
      refine ⟨ψ, hψ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hl x
      simp [hz] at h1
      exact hx h1.symm
    · rintro ⟨ψ, hψ, h0⟩
      obtain ⟨φ, hφ, hr⟩ := exists_right_inverse hψ (surjective_of_irr hirr hψ h0)
      refine ⟨φ, hφ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hr x
      simp [hz] at h1
      exact hx h1.symm
  · rintro Γ _ _ τ V _ _ _ W _ _ _ ρ σ hτ ⟨φ, hφ, h0⟩ ⟨φ', hφ', h0'⟩ hfin
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
    rw [Submodule.finrank_eq_zero] at hfin
    have hmem : φ' ∘ₗ ψ ∈ Intw ρ σ := comp_mem hψ hφ'
    rw [hfin, Submodule.mem_bot] at hmem
    apply h0'
    have h1 : (φ' ∘ₗ ψ) ∘ₗ φ = φ' := by rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]
    rw [← h1, hmem, LinearMap.zero_comp]
  · intro Γ _ _ V _ _ _ ρ h
    exact irr_of_finrank_one ρ h
  · intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ hfin
    have hne : Intw ρ σ ≠ ⊥ := fun hb => hfin (by rw [hb]; exact finrank_bot ℂ _)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).mp hne
    exact ⟨LinearEquiv.ofBijective φ
        ⟨injective_of_irr hρ hφ h0, surjective_of_irr hσ hφ h0⟩,
      fun γ v => LinearMap.congr_fun (hφ γ) v⟩
end GlobalTheory.CompanionTheory.TyFin.Maschke
