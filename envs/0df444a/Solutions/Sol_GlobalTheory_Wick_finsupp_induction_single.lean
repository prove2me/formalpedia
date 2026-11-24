-- Prove2me | solution 1 for GlobalTheory.Wick.finsupp_induction_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:49.798385+00:00
-- url     : https://prove2.me/submissions/5164e32a-b266-4698-96bf-2aa5c5cbb653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : Type*}
namespace GlobalTheory.Wick
theorem _root_.solution {p : (σ →₀ ℕ) → Prop} (h0 : p 0)
    (h : ∀ β i, p β → p (β + Finsupp.single i 1)) (β : σ →₀ ℕ) : p β := by
  induction β using Finsupp.induction with
  | zero => exact h0
  | single_add i e f _ _ hf =>
    clear * - hf h
    induction e with
    | zero => simpa using hf
    | succ e ih => rw [Finsupp.single_add, add_right_comm]; exact h _ _ ih
end GlobalTheory.Wick
