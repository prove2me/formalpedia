-- Prove2me | solution 1 for N4Code.sum_Icc0_eq_Icc1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:27.879565+00:00
-- url     : https://prove2.me/submissions/96c602dc-0dae-42dc-ad25-20d57acf6fc0

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (a : ℕ → ℝ) (ha : a 0 = 0) :
    (∑ d ∈ Finset.Icc 0 n, a d) = ∑ d ∈ Finset.Icc 1 n, a d := by
  by_cases hn : n = 0
  · subst n
    simp [ha]
  · have h01 : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
    have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
      ext d
      constructor
      · intro hd
        by_cases hd0 : d = 0
        · rw [Finset.mem_insert]
          exact Or.inl hd0
        · rw [Finset.mem_insert]
          right
          simp [Finset.mem_Icc] at hd ⊢
          omega
      · intro hd
        rw [Finset.mem_insert] at hd
        rcases hd with hd0 | hd1
        · simp [hd0]
        · simp [Finset.mem_Icc] at hd1 ⊢
          omega
    rw [hsplit, Finset.sum_insert]
    · simp [ha]
    · simp
end N4Code
