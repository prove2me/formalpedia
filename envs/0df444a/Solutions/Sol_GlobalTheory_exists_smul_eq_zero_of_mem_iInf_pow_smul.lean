-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_zero_of_mem_iInf_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:57.836417+00:00
-- url     : https://prove2.me/submissions/ec711429-6937-4bd4-8f6f-e6969e281cac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsNoetherianRing A] [Module.Finite A M]
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) {x : M}
    (hx : x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule A M)) : ∃ f : A, f - 1 ∈ I ∧ f • x = 0 := by
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).1 hx
  refine ⟨1 - r, by simp, ?_⟩
  rw [sub_smul, one_smul, hr, sub_self]
end GlobalTheory
