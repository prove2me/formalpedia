-- Prove2me | solution 1 for KnodelPrimeCordial.count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:25.785447+00:00
-- url     : https://prove2.me/submissions/c62996fc-2629-4f3e-addc-e94484f9e97f

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

theorem KnodelPrimeCordial.count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1 (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2).card = k + 1 := by
  rw [p2m_cnt_fin (6 * k + 3) (fun n => n ≠ 0 ∧ n % 6 = 2)]
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]

    split_ifs <;> omega

theorem solution (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2).card = k + 1 := by
  rw [p2m_cnt_fin (6 * k + 3) (fun n => n ≠ 0 ∧ n % 6 = 2)]
  induction k with
  | zero => decide
  | succ k ih =>
    rw [p2m_cnt_step, ih]

    split_ifs <;> omega
