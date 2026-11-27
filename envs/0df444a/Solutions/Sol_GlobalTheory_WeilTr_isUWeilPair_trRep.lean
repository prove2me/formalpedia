-- Prove2me | solution 1 for GlobalTheory.WeilTr.isUWeilPair_trRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:42.237616+00:00
-- url     : https://prove2.me/submissions/739db0b6-02f9-445e-a67a-fbdda8959c5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep
import Theorems.Thm_GlobalTheory_WeilTr_isUSplitting_trRep
import Theorems.Thm_GlobalTheory_WeilTr_isUWeilB_trRep
import Theorems.Thm_GlobalTheory_WeilTr_transpCoord_e
import Theorems.Thm_GlobalTheory_WeilM_IsUWeilPair_isUSplitting


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.WeilTr
open GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}
namespace GlobalTheory.WeilTr
theorem _root_.solution {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    (hD' : ∀ d' d₁' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) → (∀ x : Matrix α β E, d₁'.e xᵀ = d₁.e x) →
      HasDbl c C ψ ξ JB JA d' d₁' T)
    {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUWeilPair c C ψ ξ JA JB d₁ χA χB (trRep T om) := by
  have hsplit := isUSplitting_trRep hT h.isUSplitting
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  have hT' : IsGoodInt C ψ d' (transpCoord d₁) T := by
    obtain ⟨h1, h2, h3, h4⟩ := hT
    refine ⟨h1, fun w φ hφ => ?_, h3, h4⟩
    have e1 : d'.e w = d.e wᵀ := by rw [← hd', Matrix.transpose_transpose]
    have e2 : (transpCoord d₁).e w = d₁.e wᵀ := by rw [← transpCoord_e d₁ wᵀ, Matrix.transpose_transpose]
    have := h2 wᵀ φ hφ
    simp only [Darboux.rho] at this ⊢
    rw [e1, e2, this]
  exact ⟨isUWeilB_trRep hT hD hB, ⟨transpCoord d₁, transpCoord_e d₁, isUWeilB_trRep hT' (hD' d' _ hd' (transpCoord_e d₁)) hA⟩, hsplit.cont⟩
end GlobalTheory.WeilTr
