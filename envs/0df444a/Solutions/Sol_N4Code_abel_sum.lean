-- Prove2me | solution 1 for N4Code.abel_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:10.063813+00:00
-- url     : https://prove2.me/submissions/f849d4c5-84f7-4b6c-8395-d3b6d9588044

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (a : ℕ → ℝ) (r : ℝ) :
    (∑ d ∈ Finset.Icc 1 n, a d * r ^ (d - 1)) =
      (∑ i ∈ Finset.Icc 1 n, a i) * r ^ (n - 1) +
        ∑ d ∈ Finset.Icc 1 (n - 1), (∑ i ∈ Finset.Icc 1 d, a i) * (r ^ (d - 1) - r ^ d) := by
  let P : ℕ → ℝ := fun d => ∑ i ∈ Finset.Icc 1 d, a i
  have hP0 : P 0 = 0 := by simp [P]
  have hsplit : ∀ d : ℕ, 1 ≤ d → Finset.Icc 1 d = insert d (Finset.Icc 1 (d - 1)) := by
    intro d hd
    ext i
    constructor
    · intro hi
      by_cases hid : i = d
      · rw [Finset.mem_insert]
        exact Or.inl hid
      · rw [Finset.mem_insert]
        right
        simp [Finset.mem_Icc] at hi ⊢
        omega
    · intro hi
      rw [Finset.mem_insert] at hi
      rcases hi with hid | hi1
      · rw [hid]
        simp [Finset.mem_Icc] at hd ⊢
        omega
      · simp [Finset.mem_Icc] at hi1 ⊢
        omega
  have hsplit0 : ∀ m : ℕ, Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
    intro m
    ext i
    constructor
    · intro hi
      by_cases hi0 : i = 0
      · rw [Finset.mem_insert]
        exact Or.inl hi0
      · rw [Finset.mem_insert]
        right
        simp [Finset.mem_Icc] at hi ⊢
        omega
    · intro hi
      rw [Finset.mem_insert] at hi
      rcases hi with hi0 | hi1
      · simp [hi0]
      · simp [Finset.mem_Icc] at hi1 ⊢
        omega
  have hP : ∀ d : ℕ, 1 ≤ d → P d = P (d - 1) + a d := by
    intro d hd
    unfold P
    have hdmem : d ∉ Finset.Icc 1 (d - 1) := by
      simp [Finset.mem_Icc]
      omega
    rw [hsplit d hd, Finset.sum_insert hdmem]
    rw [add_comm]
  calc
    (∑ d ∈ Finset.Icc 1 n, a d * r ^ (d - 1))
        = ∑ d ∈ Finset.Icc 1 n, (P d - P (d - 1)) * r ^ (d - 1) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          rw [hP d hd1]
          ring
    _ = (∑ d ∈ Finset.Icc 1 n, P d * r ^ (d - 1)) -
        ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro d hd
          ring
    _ = P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
          by_cases hn : n = 0
          · subst n
            simp [P]
          · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
            have hsn : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := hsplit n hn1
            have hre : (∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1)) =
                ∑ e ∈ Finset.Icc 0 (n - 1), P e * r ^ e := by
              refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
              · intro d hd
                simp [Finset.mem_Icc] at hd ⊢
                omega
              · intro a ha b hb hab
                have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
                have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
                omega
              · intro e he
                refine ⟨e + 1, ?_, ?_⟩
                · simp [Finset.mem_Icc] at he ⊢
                  omega
                · omega
              · intro d hd
                simp
            calc
              (∑ d ∈ Finset.Icc 1 n, P d * r ^ (d - 1)) -
                  ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1)
                  = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                      ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1) := by
                    have hnmem : n ∉ Finset.Icc 1 (n - 1) := by
                      simp [Finset.mem_Icc]
                      omega
                    rw [hsn, Finset.sum_insert hnmem]
              _ = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  ∑ e ∈ Finset.Icc 0 (n - 1), P e * r ^ e := by
                    rw [hre]
              _ = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  (P 0 * r ^ 0 + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d) := by
                    have h0mem : 0 ∉ Finset.Icc 1 (n - 1) := by
                      simp [Finset.mem_Icc]
                    rw [hsplit0 (n - 1), Finset.sum_insert h0mem]
              _ = P n * r ^ (n - 1) + ((∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d) := by
                    rw [hP0]
                    ring
              _ = P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
                    have hsub : (∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                        ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d =
                        ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
                      rw [← Finset.sum_sub_distrib]
                      apply Finset.sum_congr rfl
                      intro d hd
                      ring
                    rw [hsub]
end N4Code
