-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.factor_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:04.288279+00:00
-- url     : https://prove2.me/submissions/885851dc-9770-4bea-bc3f-2f8ab7326e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₂) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₂ f = f) ∧ (¬Q → f * σ₂ f = 0 ∧ e = f + σ₂ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (0, e) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (0, e) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₂ : f * y₂ ≠ 0 := fun h0 => hy (Prod.ext (zero_mul y₁) h0)
    obtain ⟨z, hz⟩ := hfy y₂ hy₂
    exact ⟨(0, z), Prod.ext (mul_zero _) hz⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ 0, σ₂ f) = (0, f)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)
    rw [map_zero]
    exact ⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩
end GlobalTheory.UnitLemma.Desc
