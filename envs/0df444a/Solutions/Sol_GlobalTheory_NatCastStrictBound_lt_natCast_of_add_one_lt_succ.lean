-- Prove2me | solution 1 for GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:51.85159+00:00
-- url     : https://prove2.me/submissions/2d0e0ec7-dd61-47b8-bbd9-cc28c2ec528b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LtNatCastOfAddOneLtSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastStrictBound
namespace GlobalTheory.NatCastStrictBound
theorem _root_.solution :
    ∀ {a : WithBot ℕ∞} {n : ℕ}, a + (1 : WithBot ℕ∞) < (↑(n + (1 : ℕ)) : WithBot ℕ∞) →
      a < (↑n : WithBot ℕ∞) := by
  intro a n h
  by_contra hc
  have hle : (↑n : WithBot ℕ∞) ≤ a := not_lt.mp hc
  have h2 : (↑n : WithBot ℕ∞) + 1 ≤ a + 1 := by gcongr
  rw [Nat.cast_add, Nat.cast_one] at h
  exact absurd h (not_lt.mpr h2)
end GlobalTheory.NatCastStrictBound
