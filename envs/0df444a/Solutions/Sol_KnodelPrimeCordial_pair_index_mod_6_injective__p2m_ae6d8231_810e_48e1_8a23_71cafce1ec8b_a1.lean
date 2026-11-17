-- Prove2me | solution 1 for KnodelPrimeCordial.pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T13:10:31.897093+00:00
-- url     : https://prove2.me/submissions/d34f029f-407d-40be-bdd9-9c14f9ce9a68

import Mathlib

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.InjOn
      (fun v : Fin 2 × Fin (n / 2) =>
        if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
      Set.univ := by
  intro x hx y hy hxy
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  have hi : i.val < n / 2 := i.isLt
  have hj : j.val < n / 2 := j.isLt
  rcases hn with ⟨k, hk⟩
  have hn2 : n = 2 * (n / 2) := by omega
  have hfirst (t : Fin (n / 2)) : (2 * t.val) % n = 2 * t.val := by
    apply Nat.mod_eq_of_lt
    omega
  have hsecond (t : Fin (n / 2)) :
      (2 * t.val + n - 1) % n = if t.val = 0 then n - 1 else 2 * t.val - 1 := by
    by_cases ht : t.val = 0
    · have hval : 2 * t.val + n - 1 = n - 1 := by simp [ht]
      rw [hval]
      simpa [ht] using (Nat.mod_eq_of_lt (show n - 1 < n by omega))
    · have htpos : 0 < t.val := by omega
      have hrep : 2 * t.val + n - 1 = n + (2 * t.val - 1) := by omega
      have hlt : 2 * t.val - 1 < n := by omega
      rw [if_neg ht, hrep, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hlt]
  fin_cases a <;> fin_cases b
  all_goals
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0 <;>
      simp [hfirst, hsecond, hi0, hj0] at hxy ⊢
    all_goals
      first
      | omega
      | apply Fin.ext
        omega
