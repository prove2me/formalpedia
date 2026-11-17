-- Prove2me | solution 2 for KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:26.676531+00:00
-- url     : https://prove2.me/submissions/bb585e77-717e-4f00-beba-439c25946742

import Mathlib
theorem p2m_cnt_fin (N : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (Finset.univ.filter fun j : Fin N => q j.val).card = ((Finset.range N).filter q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if q i then 1 else 0) N

theorem p2m_cnt_step (k : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ((Finset.range (6 * (k + 1) + 3)).filter q).card =
      ((Finset.range (6 * k + 3)).filter q).card +
      ((if q (6 * k + 3) then 1 else 0) + (if q (6 * k + 4) then 1 else 0) +
       (if q (6 * k + 5) then 1 else 0) + (if q (6 * k + 6) then 1 else 0) +
       (if q (6 * k + 7) then 1 else 0) + (if q (6 * k + 8) then 1 else 0)) := by
  rw [Finset.card_filter, Finset.card_filter,
    show 6 * (k + 1) + 3 = 6 * k + 3 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
  simp only [Finset.sum_range_succ]
  ring_nf

theorem KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1 (n : ℕ) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (n + 2) / 4 := by
  rw [p2m_cnt_fin (n / 2) (fun n => n ≠ 0 ∧ n % 6 ∈ ({1, 2, 4} : Finset ℕ))]
  obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 6 := ⟨n / 12, by omega⟩
  rw [show (12 * k + 6) / 2 = 6 * k + 3 by omega, show (12 * k + 6 + 2) / 4 = 3 * k + 2 by omega]
  clear hmod
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> omega

theorem solution (n : ℕ) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (n + 2) / 4 := by
  rw [p2m_cnt_fin (n / 2) (fun n => n ≠ 0 ∧ n % 6 ∈ ({1, 2, 4} : Finset ℕ))]
  obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 6 := ⟨n / 12, by omega⟩
  rw [show (12 * k + 6) / 2 = 6 * k + 3 by omega, show (12 * k + 6 + 2) / 4 = 3 * k + 2 by omega]
  clear hmod
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> omega
