-- Prove2me | solution 1 for GlobalTheory.DegreeBound.common_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:15.682305+00:00
-- url     : https://prove2.me/submissions/9460ef74-d484-45c5-9075-2c04eff446a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
import Theorems.Thm_GlobalTheory_DegreeBound_good_mono
import Theorems.Thm_GlobalTheory_DegreeBound_good_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}
namespace GlobalTheory.DegreeBound
theorem _root_.solution {y : Fin D → K} {j : Fin D} (c : ℕ → K) (hc : ∀ k, ∃ N, Good y j N (c k))
    (n : ℕ) : ∃ N, ∀ k < n, Good y j N (c k) := by
  induction n with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := hc n
    refine ⟨N + M, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact good_mono (hN k hk) M
    · exact good_le hM (Nat.le_add_left _ _)
end GlobalTheory.DegreeBound
