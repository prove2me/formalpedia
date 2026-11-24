-- Prove2me | solution 1 for GlobalTheory.existsUnique_endo_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:09.680327+00:00
-- url     : https://prove2.me/submissions/96d6bc0a-b5de-447d-879a-1e5a9e0c741a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodValuationBound
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : ι → Submodule K V) (hW : DirectSum.IsInternal W) (τ : ι) (v w : V) (hv : v ∈ W τ) (hv0 : v ≠ 0)
    (h1 : Module.finrank K (W τ) = 1) :
    ∃! N : Module.End K V, N v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N x = 0 := by
  have hspan : ∀ x ∈ W τ, ∃ c : K, c • v = x := by
    intro x hx
    have hu : (⟨v, hv⟩ : W τ) ≠ 0 := by simpa using hv0
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : W τ) hu).1 h1 ⟨x, hx⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  have hind := hW.submodule_iSupIndep
  have htop := hW.submodule_iSup_eq_top
  set C : Submodule K V := ⨆ j, ⨆ (_ : j ≠ τ), W j with hC
  have hmemC : ∀ σ, σ ≠ τ → ∀ x ∈ W σ, x ∈ C := fun σ hσ x hx =>
    (le_iSup₂_of_le σ hσ le_rfl : W σ ≤ C) hx
  have hc : IsCompl (W τ) C := by
    refine ⟨hind τ, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine iSup_le fun j => ?_
    by_cases hj : j = τ
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  have huniq : ∀ N₁ N₂ : Module.End K V, (N₁ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₁ x = 0) →
      (N₂ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₂ x = 0) → N₁ = N₂ := by
    intro N₁ N₂ h₁ h₂
    have hle : ∀ σ, W σ ≤ LinearMap.eqLocus N₁ N₂ := by
      intro σ x hx
      show N₁ x = N₂ x
      by_cases hσ : σ = τ
      · subst hσ
        obtain ⟨c, rfl⟩ := hspan x hx
        rw [map_smul, map_smul, h₁.1, h₂.1]
      · rw [h₁.2 σ hσ x hx, h₂.2 σ hσ x hx]
    have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus N₁ N₂ := htop ▸ iSup_le hle
    exact LinearMap.ext fun x => this (Submodule.mem_top)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K V v)
    (LinearMap.ker_toSpanSingleton K hv0)
  let p := Submodule.linearProjOfIsCompl (W τ) C hc
  have hN0 : ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) v = w ∧
      ∀ σ, σ ≠ τ → ∀ x ∈ W σ, ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) x = 0 := by
    constructor
    · have hpv : p v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩
      have hgv : g v = 1 := by simpa using LinearMap.congr_fun hg 1
      simp [hpv, hgv]
    · intro σ hσ x hx
      have : p x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (hmemC σ hσ x hx)
      simp [this]
  exact ⟨_, hN0, fun N hN => huniq _ _ hN hN0⟩
end GlobalTheory
