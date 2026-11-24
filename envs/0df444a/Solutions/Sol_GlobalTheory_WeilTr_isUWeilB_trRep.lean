-- Prove2me | solution 1 for GlobalTheory.WeilTr.isUWeilB_trRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:03.790629+00:00
-- url     : https://prove2.me/submissions/8b188b57-ab5d-4b7b-a569-6131fbed01da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep
import Theorems.Thm_GlobalTheory_WeilTr_trRep_apply
import Theorems.Thm_GlobalTheory_WeilTr_isUSplitting_trRep
import Theorems.Thm_GlobalTheory_WeilTr_siegelRule_trRep

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
    {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsUWeilB c C ψ ξ JA JB d₁ χ (trRep T om) := by
  obtain ⟨hs, dd, omd, hdd, ⟨hL, hsd, hsg⟩, hbox⟩ := h
  obtain ⟨dd₁, Td, S, hdd₁, hTd, hS, hTbox⟩ := hD dd hdd
  have hinvT : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hT.1 _).2 (by simpa using hφ)
  have hinvS : ∀ φ ∈ C.sp κ, S.symm φ ∈ C.sp κ := fun φ hφ => (hS _).2 (by simpa using hφ)
  refine ⟨isUSplitting_trRep hT hs, dd₁, trRep Td omd, hdd₁, ⟨hL, isUSplitting_trRep hTd hsd, siegelRule_trRep hTd hsg⟩, fun g gd hg φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have hb : Td.symm (boxFun φ₁ φ₂) = boxFun (T.symm φ₁) (S.symm φ₂) := by
    rw [LinearEquiv.symm_apply_eq, hTbox _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [trRep_apply, hb, hbox g gd hg _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂),
    hTbox _ (hs.pres g _ (hinvT φ₁ hφ₁)) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply, trRep_apply]
end GlobalTheory.WeilTr
