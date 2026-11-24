-- Prove2me | solution 1 for GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:32.443252+00:00
-- url     : https://prove2.me/submissions/65323c5e-f4e2-4533-9e8e-93f8de028949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NoethLocalHausdorff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherianLocalHausdorff
namespace GlobalTheory.NoetherianLocalHausdorff
theorem _root_.solution : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by
  intro B _ _ _
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top] at h
  exact (Submodule.mem_bot B).1 h
end GlobalTheory.NoetherianLocalHausdorff
