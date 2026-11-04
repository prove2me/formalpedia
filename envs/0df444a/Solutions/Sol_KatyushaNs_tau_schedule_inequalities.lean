-- Prove2me | solution 1 for KatyushaNs.tau_schedule_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:34:21.227328+00:00
-- url     : https://prove2.me/submissions/5d969e86-c1b3-43cb-b360-a49e9c540991

import Definitions.Def_KatyushaNs_tau1
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open KatyushaNs

theorem solution (s : ℕ) :
    tau1 s ≤ 1 / 2 ∧
      (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ≤ 1 / tau1 s ^ 2 ∧
      (1 / 2) / tau1 (s + 1) ^ 2 ≤ (tau1 s + 1 / 2) / tau1 s ^ 2 := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have h4 : (s : ℝ) + 4 ≠ 0 := ne_of_gt (by linarith)
  have h5 : (s : ℝ) + 5 ≠ 0 := ne_of_gt (by linarith)
  have ht : tau1 s = 2 / ((s : ℝ) + 4) := rfl
  have ht' : tau1 (s + 1) = 2 / ((s : ℝ) + 5) := by
    simp only [tau1, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hfirst : tau1 s ≤ 1 / 2 := by
    rw [ht]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < s + 4)).2
    linarith
  have hinv : 1 / tau1 s ^ 2 = ((s : ℝ) + 4) ^ 2 / 4 := by
    rw [ht]
    field_simp <;> norm_num
  have hleft : (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 =
      (((s : ℝ) + 5) * ((s : ℝ) + 3)) / 4 := by
    rw [ht']
    field_simp [h5]
    ring
  have hhalf : (1 / 2) / tau1 (s + 1) ^ 2 = ((s : ℝ) + 5) ^ 2 / 8 := by
    rw [ht']
    field_simp <;> norm_num
  have hright : (tau1 s + 1 / 2) / tau1 s ^ 2 =
      (((s : ℝ) + 4) ^ 2 + 4 * ((s : ℝ) + 4)) / 8 := by
    rw [ht]
    field_simp [h4]
    ring
  refine ⟨hfirst, ?_, ?_⟩
  · rw [hleft, hinv]
    nlinarith
  · rw [hhalf, hright]
    nlinarith

#print axioms solution

