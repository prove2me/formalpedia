-- Prove2me | solution 1 for McNaughtonSched.SingleProc.pair_interchange
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:07:29.701319+00:00
-- url     : https://prove2.me/submissions/a76b7543-3cdb-43de-b23d-ef9f009ce78f

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model



namespace McNaughtonSched.SingleProc

theorem pair_interchange_core {m : ℕ} (a p d : Fin m → ℝ) (i j : Fin m)
    (hai : 0 < a i) (haj : 0 < a j) (hr : p j / a j < p i / a i)
    (t : ℝ) (hdi : d i ≤ t) (hdj : d j ≤ t) :
    taskLoss p d i (t + a i) + taskLoss p d j (t + a i + a j) <
      taskLoss p d j (t + a j) + taskLoss p d i (t + a j + a i) := by
  rw [div_lt_div_iff₀ haj hai] at hr
  unfold taskLoss
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  nlinarith

theorem completion_nonneg' {m : ℕ} (S : Schedule m) (i : Fin m) : 0 ≤ completion S i := by
  unfold completion
  induction ((S.filter fun g => g.task = i).map Piece.stop) with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem loss_diff_core {m : ℕ} (a p d : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i)
    (S' : Schedule m) :
    totalLoss p 0 S' - totalLoss p 0 (seqSchedule a σ) ≤
      totalLoss p d S' - totalLoss p d (seqSchedule a σ) := by
  unfold totalLoss
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  unfold taskLoss
  have h1 := completion_nonneg' S' i
  have h2 := completion_nonneg' (seqSchedule a σ) i
  have h3 := hlate i
  simp only [Pi.zero_apply, sub_zero]
  rw [max_eq_right h1, max_eq_right h2, max_eq_right (show 0 ≤ completion (seqSchedule a σ) i - d i by linarith)]
  have := hp i
  have h4 : completion S' i - d i ≤ max 0 (completion S' i - d i) := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left h4 (hp i)]

end McNaughtonSched.SingleProc

open McNaughtonSched.SingleProc


theorem solution {m : ℕ} (a p d : Fin m → ℝ) (i j : Fin m)
    (hai : 0 < a i) (haj : 0 < a j) (hr : p j / a j < p i / a i)
    (t : ℝ) (hdi : d i ≤ t) (hdj : d j ≤ t) :
    taskLoss p d i (t + a i) + taskLoss p d j (t + a i + a j) <
      taskLoss p d j (t + a j) + taskLoss p d i (t + a j + a i) := by
  exact pair_interchange_core a p d i j hai haj hr t hdi hdj
