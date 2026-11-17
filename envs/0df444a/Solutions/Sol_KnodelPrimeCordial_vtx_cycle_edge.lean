-- Prove2me | solution 1 for KnodelPrimeCordial.vtx_cycle_edge
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T08:24:28.129648+00:00
-- url     : https://prove2.me/submissions/1da6c004-d375-4853-8e95-71ff90a5b87d

import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_vtx

open KnodelPrimeCordial

theorem solution (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) (a b : Fin n)
    (hab : b.val = (a.val + 1) % n) :
    (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) := by
  have hn2 : n = 2 * (n / 2) := by rcases hn with ⟨k, hk⟩; omega
  have ha := a.isLt
  have hb := b.isLt
  by_cases hend : a.val + 1 = n
  · have hb0 : b.val = 0 := by rw [hend, Nat.mod_self] at hab; exact hab
    have haodd : a.val % 2 ≠ 0 := by omega
    have hbeven : b.val % 2 = 0 := by omega
    simp only [knodel, vtx, haodd, hbeven, if_false, if_true]
    right
    refine ⟨trivial, trivial, 0, by decide, ?_⟩
    simp [hend, hb0]
  · have hab' : b.val = a.val + 1 := by
      rw [Nat.mod_eq_of_lt (by omega)] at hab
      exact hab
    by_cases heven : a.val % 2 = 0
    · have hbodd : b.val % 2 ≠ 0 := by omega
      have hhalf : (b.val + 1) / 2 = a.val / 2 + 1 := by omega
      simp only [knodel, vtx, heven, hbodd, if_false, if_true]
      left
      refine ⟨trivial, trivial, 1, by decide, ?_⟩
      simp only [hhalf]
      norm_num
    · have hbeven : b.val % 2 = 0 := by omega
      have hhalf : (a.val + 1) / 2 = b.val / 2 := by omega
      simp only [knodel, vtx, heven, hbeven, if_false, if_true]
      right
      refine ⟨trivial, trivial, 0, by decide, ?_⟩
      simp [hhalf]
