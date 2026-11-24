-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.traceDual_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:02.198588+00:00
-- url     : https://prove2.me/submissions/d8601244-37f5-4240-b52d-f072aec9f641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).traceDual k ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_traceDual]
  intro a ha
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
  have h := ((integralBasis E).traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E y) k
  rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply] at h
  rw [Algebra.traceForm_apply, mul_comm, ← Algebra.traceForm_apply, ← h]
  exact ⟨_, rfl⟩
end GlobalTheory.ColengthDifferent
