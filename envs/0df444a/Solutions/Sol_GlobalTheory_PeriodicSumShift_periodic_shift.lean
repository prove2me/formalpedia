-- Prove2me | solution 1 for GlobalTheory.PeriodicSumShift.periodic_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:31.190604+00:00
-- url     : https://prove2.me/submissions/fb2ca5e2-0329-4a7a-ba10-0c8dd4f175bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumRangeMulOfPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PeriodicSumShift
namespace GlobalTheory.PeriodicSumShift
theorem _root_.solution {K : Type} (g : ℕ → K) (N : ℕ) (h : ∀ i, g (N + i) = g i) :
    ∀ k i, g (N * k + i) = g i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih => intro i; rw [Nat.mul_succ, add_assoc, ih, h]
end GlobalTheory.PeriodicSumShift
