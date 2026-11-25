-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_prime_pow_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:50.827947+00:00
-- url     : https://prove2.me/submissions/5c2c498f-3d5c-48b1-842f-20293098b7d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
import Theorems.Thm_GlobalTheory_BadShare_sum_le_prod_of_two_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare
private theorem prod_prime_pow_dvd_of_forall_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ)
    (hp : ∀ l ∈ s, l.Prime) (hd : ∀ l ∈ s, l ^ e l ∣ M) : ∏ l ∈ s, l ^ e l ∣ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self a s))
      (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) (fun l hl => hd l (Finset.mem_insert_of_mem hl)))
    refine Nat.Coprime.prod_right fun l hl => ?_
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self a s)) (hp l (Finset.mem_insert_of_mem hl))).mpr
      (by rintro rfl; exact ha hl)
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hM : M ≠ 0)
    (hp : ∀ l ∈ s, l.Prime) (he : ∀ l ∈ s, e l ≠ 0) (hd : ∀ l ∈ s, l ^ e l ∣ M) :
    ∑ l ∈ s, l ^ e l ≤ M := by
  have h2 : ∀ l ∈ s, 2 ≤ l ^ e l := fun l hl => le_trans (hp l hl).two_le (Nat.le_self_pow (he l hl) l)
  exact (sum_le_prod_of_two_le s _ h2).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (prod_prime_pow_dvd_of_forall_dvd s e M hp hd))
end GlobalTheory.BadShare
