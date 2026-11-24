-- Prove2me | solution 1 for GlobalTheory.WeilTr.siegelRule_trRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:33.397277+00:00
-- url     : https://prove2.me/submissions/eb7c7e5f-6c29-4d25-acc5-8121277b655b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep
import Theorems.Thm_GlobalTheory_WeilTr_trRep_apply

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
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) : SiegelRule c C ψ ξ JA JB d₁ χ Cy (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, -⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  intro l hl hinvl p t hpt φ hφ
  have key := h (l ∘ₗ T.toLinearMap) ((hadm l).1 hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hheis _ _ hφ', hinvl z _ ((hsp _).1 hφ')]) p t hpt (T.symm φ) (hinv φ hφ)
  simpa [trRep_apply] using key
end GlobalTheory.WeilTr
