-- Prove2me | solution 1 for GlobalTheory.TracedComatrix.epow_succ_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:58.943058+00:00
-- url     : https://prove2.me/submissions/f2e236ea-f0b3-4c05-ad8b-a8480b526eb9

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TracedQminorComatrixTruncatedInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.TracedComatrix
namespace GlobalTheory.TracedComatrix
theorem _root_.solution {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, E a c * epow E k c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [epow]
  | succ k ih =>
    intro a b
    calc epow E (k + 1 + 1) a b = ∑ c, epow E (k + 1) a c * E c b := rfl
      _ = ∑ c, (∑ d, E a d * epow E k d c) * E c b :=
          Finset.sum_congr rfl fun c _ => by rw [ih a c]
      _ = ∑ d, E a d * ∑ c, epow E k d c * E c b := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ d, E a d * epow E (k + 1) d b := rfl
end GlobalTheory.TracedComatrix
