-- Prove2me | solution 1 for GlobalTheory.UnramSub.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:06.287021+00:00
-- url     : https://prove2.me/submissions/43342296-5e85-43fc-b4d1-bb0740f061cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}
namespace GlobalTheory.UnramSub
theorem _root_.solution {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by
  obtain ⟨_, f₁, hf₁, hi₁⟩ := h₁
  obtain ⟨_, f₂, hf₂, hi₂⟩ := h₂
  refine ⟨‹_›, f₂.comp f₁, fun v => ?_, fun π hπ => hi₂ _ (hi₁ π hπ)⟩
  rw [RingHom.comp_apply, hf₂, Subring.coe_subtype, hf₁]
end GlobalTheory.UnramSub
