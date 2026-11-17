-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_residue_5_index_count__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:27.683842+00:00
-- url     : https://prove2.me/submissions/4bd19278-7bbb-4ae2-b54f-6268e4ec2482

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

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_5_index_count__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 5).card = n / 12 := by
  rw [p2m_cnt_fin (n / 2) (fun n => n % 6 = 5)]
  obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 6 := ⟨n / 12, by omega⟩
  rw [show (12 * k + 6) / 2 = 6 * k + 3 by omega, show (12 * k + 6) / 12 = k by omega]
  clear hmod hn h10
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]
    split_ifs <;> omega

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 5).card = n / 12 := by
  rw [p2m_cnt_fin (n / 2) (fun n => n % 6 = 5)]
  obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 6 := ⟨n / 12, by omega⟩
  rw [show (12 * k + 6) / 2 = 6 * k + 3 by omega, show (12 * k + 6) / 12 = k by omega]
  clear hmod hn h10
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]
    split_ifs <;> omega
