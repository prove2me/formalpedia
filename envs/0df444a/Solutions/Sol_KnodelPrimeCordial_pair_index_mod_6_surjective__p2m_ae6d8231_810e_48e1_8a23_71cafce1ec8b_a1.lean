-- Prove2me | solution 1 for KnodelPrimeCordial.pair_index_mod_6_surjective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:57:33.194195+00:00
-- url     : https://prove2.me/submissions/3abb968a-6f19-44a9-8ac0-9a99d95e39c8

import Mathlib

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.SurjOn
      (fun v : Fin 2 × Fin (n / 2) =>
        if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
      Set.univ (Set.Icc 0 (n - 1)) := by
  intro y hy
  rcases Set.mem_Icc.mp hy with ⟨_, hyupper⟩
  have hyn : y < n := by omega
  have hneven : n % 2 = 0 := by
    rcases hn with ⟨k, hk⟩
    omega
  by_cases he : y % 2 = 0
  · have hyEq : 2 * (y / 2) = y := by omega
    have hk : y / 2 < n / 2 := by omega
    refine ⟨(0, ⟨y / 2, hk⟩), Set.mem_univ _, ?_⟩
    change (2 * (y / 2)) % n = y
    rw [hyEq, Nat.mod_eq_of_lt hyn]
  · by_cases hb : y = n - 1
    · have hk : 0 < n / 2 := by omega
      refine ⟨(1, ⟨0, hk⟩), Set.mem_univ _, ?_⟩
      change (2 * 0 + n - 1) % n = y
      rw [show 2 * 0 + n - 1 = n - 1 by omega]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hb.symm
    · have hyEq : 2 * ((y + 1) / 2) = y + 1 := by omega
      have hk : (y + 1) / 2 < n / 2 := by omega
      refine ⟨(1, ⟨(y + 1) / 2, hk⟩), Set.mem_univ _, ?_⟩
      change (2 * ((y + 1) / 2) + n - 1) % n = y
      rw [show 2 * ((y + 1) / 2) + n - 1 = y + n by omega]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hyn]
