-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:04.714439+00:00
-- url     : https://prove2.me/submissions/97357581-1e20-4942-ba79-3ffbd87a79fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution : PP PEmpty := by
  intro _ M _ _ Op K _ _ _
  refine simpleOver_of_equiv (PiTensorProduct.isEmptyEquiv PEmpty) _ (∅ : Set (Module.End ℂ ℂ))
    _ ⊥ ?_ (by simp) ?_
  · have : piKer K = ⊥ := by
      rw [piKer, Submodule.span_eq_bot]
      rintro _ ⟨y, ⟨i, _⟩, _⟩
      exact i.elim
    rw [this, Submodule.map_bot]
  · intro N _ _
    rcases Ideal.eq_bot_or_top (N : Ideal ℂ) with h | h
    · exact Or.inl h
    · exact Or.inr h
end GlobalTheory.PiSimple
