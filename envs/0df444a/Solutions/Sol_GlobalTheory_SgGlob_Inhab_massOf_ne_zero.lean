-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.massOf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:01.957817+00:00
-- url     : https://prove2.me/submissions/556c4ff8-63f8-4f4d-90b8-f6197accad65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution {G X : Type} {C : Set X} {iso : G → X → X → Prop} (hC : C.Nonempty)
    (hf : ∀ x ∈ C, Finite {γ : G // iso γ x x}) : massOf C iso ≠ 0 := by
  obtain ⟨x, hx⟩ := hC
  rw [massOf, Ne, ENNReal.tsum_eq_zero]
  intro h
  have h1 := h (Quot.mk _ ⟨x, hx⟩)
  rw [ENNReal.inv_eq_zero, ENat.toENNReal_eq_top, ENat.card_eq_top] at h1
  exact h1.not_finite (hf _ (Quot.out (Quot.mk (fun x y : C => ∃ γ, iso γ x.1 y.1) ⟨x, hx⟩)).2)
end GlobalTheory.SgGlob.Inhab
