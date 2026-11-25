-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_add_pow_prime_pow_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:40.054848+00:00
-- url     : https://prove2.me/submissions/4da92bf6-86d9-4d1d-ac0c-a7fd554d2ad6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Ideal WittVector IsLocalRing
variable {A : Type*} [CommRing A]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {p : ℕ} (hp : p.Prime) (y : A) (N r k : ℕ)
    (hk : k ≤ p ^ r) :
    (1 + y) ^ (p ^ N) - 1 ∈ span {(p : A) ^ (N - r)} ⊔ span {y ^ k} := by
  rw [add_comm, add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun j hj => ?_
  by_cases hjk : k ≤ j + 1
  · exact Ideal.mem_sup_right (mul_mem_right _ _ (mem_span_singleton.2 (pow_dvd_pow y hjk)))
  · apply Ideal.mem_sup_left
    have hj' : j + 1 ≤ p ^ N := Finset.mem_range.1 hj
    have h1 : (j + 1).factorization p < r := by
      have h2 : p ^ (j + 1).factorization p ≤ j + 1 :=
        Nat.le_of_dvd (Nat.succ_pos j) (Nat.ordProj_dvd (j + 1) p)
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h2 (by omega))
    have h3 : p ^ (N - r) ∣ Nat.choose (p ^ N) (j + 1) := by
      have h4 := Nat.factorization_choose_prime_pow hp hj' (Nat.succ_ne_zero j)
      refine (Nat.pow_dvd_pow p (by omega : N - r ≤ N - (j + 1).factorization p)).trans ?_
      rw [← h4]
      exact Nat.ordProj_dvd _ p
    refine mul_mem_left _ _ (mem_span_singleton.2 ?_)
    exact_mod_cast Nat.cast_dvd_cast (α := A) h3
end GroundTheory.PAdicHodge
