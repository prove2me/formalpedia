-- Prove2me | solution 1 for KnodelPrimeCordial.vtx_adj_off_cycle
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T08:29:21.009062+00:00
-- url     : https://prove2.me/submissions/063a6d64-f16c-4d9e-8966-fa1b2cba1144

import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_vtx

open KnodelPrimeCordial

private theorem exists_three (P : ℕ → Prop) :
    (∃ k, k < 3 ∧ P k) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨k, hk, hp⟩
    interval_cases k <;> tauto
  · rintro (h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩

private theorem mod_twice (x m : ℕ) (h : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
theorem solution (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) (a b : Fin n)
    (hab : b.val ≠ (a.val + 1) % n) (hba : a.val ≠ (b.val + 1) % n) :
    (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) ↔
      a ≠ b ∧ ((Even a.val ∧ b.val = (a.val + 5) % n) ∨
        (Even b.val ∧ a.val = (b.val + 5) % n)) := by
  have hn2 : n = 2 * (n / 2) := by rcases hn with ⟨k, hk⟩; omega
  have ha := a.isLt
  have hb := b.isLt
  have hne : a ≠ b ↔ a.val ≠ b.val := not_congr Fin.ext_iff
  simp only [knodel, vtx, exists_three, Nat.even_iff, hne]
  split_ifs <;> norm_num
  all_goals
    simp only [mod_twice (a.val + 1) n (by omega),
      mod_twice (b.val + 1) n (by omega),
      mod_twice (a.val + 5) n (by omega),
      mod_twice (b.val + 5) n (by omega),
      Nat.mod_eq_of_lt (show a.val / 2 < n / 2 by omega),
      Nat.mod_eq_of_lt (show b.val / 2 < n / 2 by omega),
      mod_twice ((a.val + 1) / 2) (n / 2) (by omega),
      mod_twice ((b.val + 1) / 2) (n / 2) (by omega),
      mod_twice (a.val / 2 + 1) (n / 2) (by omega),
      mod_twice (b.val / 2 + 1) (n / 2) (by omega),
      mod_twice (a.val / 2 + 3) (n / 2) (by omega),
      mod_twice (b.val / 2 + 3) (n / 2) (by omega)] at *
    split_ifs at * <;> omega
