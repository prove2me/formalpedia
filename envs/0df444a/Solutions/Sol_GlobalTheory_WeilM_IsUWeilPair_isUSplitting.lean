-- Prove2me | solution 1 for GlobalTheory.WeilM.IsUWeilPair.isUSplitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:05.548195+00:00
-- url     : https://prove2.me/submissions/8ce514ce-20a2-45a3-9034-582b04b4af65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable [TopologicalSpace R] [TopologicalSpace E]
variable {c} [IsModuleTopology R E] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
variable {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
namespace GlobalTheory.WeilM
namespace IsUWeilPair
theorem _root_.solution (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUSplitting C ψ d (actAB c) om := by
  obtain ⟨⟨hB, -⟩, ⟨d', h2, hA, -⟩, hc⟩ := h
  have e : ∀ (p : UG c JA × UG c JB) φ, om p φ =
      om.comp (MonoidHom.inl _ _) p.1 (om.comp (MonoidHom.inr _ _) p.2 φ) := fun p φ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  have r : ∀ w, d.rho ψ w = d'.rho ψ wᵀ := fun w => by rw [Darboux.rho, Darboux.rho, h2]
  refine ⟨⟨fun p φ hφ => ?_, fun p w φ hφ => ?_, fun p l hl => ?_⟩, fun μ hμ p φ hφ => ?_, hc⟩
  · rw [e]; exact hA.pres _ _ (hB.pres _ _ hφ)
  · rw [e, e, hB.impl _ _ _ hφ, r, hA.impl _ _ _ (hB.pres _ _ hφ), r]
    simp only [actB, actAB, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  · rw [show l ∘ₗ om p = (l ∘ₗ om.comp (MonoidHom.inl _ _) p.1) ∘ₗ om.comp (MonoidHom.inr _ _) p.2 from
      LinearMap.ext fun φ => congrArg l (e p φ)]
    exact hB.adm _ _ (hA.adm _ _ hl)
  · rw [e, hA.unit μ hμ _ _ (hB.pres _ _ hφ), hB.unit μ hμ _ _ hφ]
end IsUWeilPair
end GlobalTheory.WeilM
