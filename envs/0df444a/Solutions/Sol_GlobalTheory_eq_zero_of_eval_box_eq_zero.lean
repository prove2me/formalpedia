-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_eval_box_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:00.791098+00:00
-- url     : https://prove2.me/submissions/f415e239-5a69-41f7-a999-e9576b8b68f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]
namespace GlobalTheory
theorem _root_.solution (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))
end GlobalTheory
