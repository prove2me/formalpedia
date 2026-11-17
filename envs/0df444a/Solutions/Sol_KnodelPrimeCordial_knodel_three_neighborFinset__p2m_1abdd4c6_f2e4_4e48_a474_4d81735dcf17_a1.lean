-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:06:13.778185+00:00
-- url     : https://prove2.me/submissions/2707ad62-ab64-44aa-bc85-f90c731cf60f

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
theorem KnodelPrimeCordial.knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).neighborFinset (0, j) = {(1, j), (1, ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩), (1, ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
  have hj := j.isLt
  ext ⟨a, b⟩
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq]
  constructor
  · rintro (⟨-, ha, k, hk, hb⟩ | ⟨-, h1, -⟩)
    · interval_cases k
      · left; refine ⟨ha, Fin.ext ?_⟩
        rw [hb]; simp [Nat.mod_eq_of_lt hj]
      · right; left; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
      · right; right; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
    · exact absurd h1 (by decide)
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · left; refine ⟨by simp, ha, 0, by norm_num, ?_⟩
      rw [hb]; simp [Nat.mod_eq_of_lt hj]
    · left; refine ⟨by simp, ha, 1, by norm_num, ?_⟩
      rw [hb]; norm_num
    · left; refine ⟨by simp, ha, 2, by norm_num, ?_⟩
      rw [hb]; norm_num

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).neighborFinset (0, j) = {(1, j), (1, ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩), (1, ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩)} := by
  have hj := j.isLt
  ext ⟨a, b⟩
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  simp only [KnodelPrimeCordial.knodel, Prod.mk.injEq]
  constructor
  · rintro (⟨-, ha, k, hk, hb⟩ | ⟨-, h1, -⟩)
    · interval_cases k
      · left; refine ⟨ha, Fin.ext ?_⟩
        rw [hb]; simp [Nat.mod_eq_of_lt hj]
      · right; left; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
      · right; right; exact ⟨ha, Fin.ext (by rw [hb]; norm_num)⟩
    · exact absurd h1 (by decide)
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · left; refine ⟨by simp, ha, 0, by norm_num, ?_⟩
      rw [hb]; simp [Nat.mod_eq_of_lt hj]
    · left; refine ⟨by simp, ha, 1, by norm_num, ?_⟩
      rw [hb]; norm_num
    · left; refine ⟨by simp, ha, 2, by norm_num, ?_⟩
      rw [hb]; norm_num

