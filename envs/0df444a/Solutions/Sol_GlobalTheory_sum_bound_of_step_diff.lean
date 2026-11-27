-- Prove2me | solution 1 for GlobalTheory.sum_bound_of_step_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:36.118992+00:00
-- url     : https://prove2.me/submissions/ef252fcc-2210-491a-b006-32fcd487b570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumBoundOfStepDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (a : ℕ → ℕ) (d p C : ℕ), 1 ≤ p →
      (∀ m : ℕ, a (m + p) ≤ a m + C * (d * (m + p + 1) ^ (d - 1))) →
      ∃ C' : ℕ, ∀ m : ℕ, a m ≤ C' * ((d + 1) * (m + 1) ^ d) := by
  intro a d p C hp h
  have key : ∀ m : ℕ, a m ≤ (∑ j ∈ Finset.range p, a j) + C * (d * (m + 1) ^ (d - 1)) * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < p
      · exact le_trans (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)) (Nat.le_add_right _ _)
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + p := ⟨m - p, by omega⟩
        have h1 := ih n (by omega)
        have h2 := h n
        have h3 : C * (d * (n + 1) ^ (d - 1)) * n ≤ C * (d * (n + p + 1) ^ (d - 1)) * n := by
          gcongr
          omega
        have h4 : C * (d * (n + p + 1) ^ (d - 1)) * (n + 1)
            ≤ C * (d * (n + p + 1) ^ (d - 1)) * (n + p) := by
          gcongr
        rw [Nat.mul_succ] at h4
        omega
  refine ⟨(∑ j ∈ Finset.range p, a j) + C, fun m => (key m).trans ?_⟩
  have h1 : 1 ≤ (d + 1) * (m + 1) ^ d := Nat.succ_le_of_lt (by positivity)
  have h2 : d * (m + 1) ^ (d - 1) * m ≤ (d + 1) * (m + 1) ^ d := by
    cases d with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, mul_assoc]
      gcongr <;> omega
  rw [add_mul, mul_assoc C]
  exact add_le_add (Nat.le_mul_of_pos_right _ h1) (Nat.mul_le_mul_left _ h2)
end GlobalTheory
