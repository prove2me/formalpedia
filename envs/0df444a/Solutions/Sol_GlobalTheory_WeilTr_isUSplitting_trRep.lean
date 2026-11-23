-- Prove2me | solution 1 for GlobalTheory.WeilTr.isUSplitting_trRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:18.343141+00:00
-- url     : https://prove2.me/submissions/b1686a0d-f499-4b06-b8b1-7eea41f18689

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
theorem _root_.solution {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ} {d d₁ : Darboux B κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUSplitting C ψ d act om) : IsUSplitting C ψ d₁ act (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  have hrho : ∀ w, ∀ φ ∈ C.sp κ, T.symm (d₁.rho ψ w φ) = d.rho ψ w (T.symm φ) := fun w φ hφ => by
    rw [LinearEquiv.symm_apply_eq, hheis w _ (hinv φ hφ), LinearEquiv.apply_symm_apply]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ hμ g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [trRep_apply]
    exact (hsp _).1 (h.pres g _ (hinv φ hφ))
  · rw [trRep_apply, trRep_apply, hrho w φ hφ, h.impl g w _ (hinv φ hφ), hheis _ _ (h.pres g _ (hinv φ hφ))]
  · have h1 : l ∘ₗ T.toLinearMap ∈ C.adm κ := (hadm l).1 hl
    have h2 := h.adm g _ h1
    have h3 : (l ∘ₗ T.toLinearMap ∘ₗ om g) ∘ₗ T.symm.toLinearMap ∈ C.adm κ := by
      rw [hadm]
      convert h2 using 1
      ext φ
      simp
    convert h3 using 1
    ext φ
    simp [trRep_apply]
  · obtain ⟨c, hc⟩ := hunit μ hμ
    rw [trRep_apply, hc _ (h.pres g _ (hinv φ hφ)), h.unit μ hμ g _ (hinv φ hφ)]
    conv_rhs => rw [← LinearEquiv.apply_symm_apply T φ]
    rw [hc _ (hinv φ hφ)]
  · have := h.cont _ ((hadm l).1 hl) _ (hinv φ hφ)
    simpa [trRep_apply] using this
end GlobalTheory.WeilTr
