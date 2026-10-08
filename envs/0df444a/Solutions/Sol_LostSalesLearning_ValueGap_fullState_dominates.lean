-- Prove2me | solution 1 for LostSalesLearning.ValueGap.fullState_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:30:30.821092+00:00
-- url     : https://prove2.me/submissions/c1f8a894-04c0-41f4-b015-f47d6eb13c48

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

open LostSalesLearning.ValueGap in
theorem solution {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) :
    Dominates (fullState L x) s := by
  obtain ⟨hnn, hsum⟩ := hs
  have hfs : ∑ i, fullState L x i = x := by
    rw [Fin.sum_univ_succ]
    simp [fullState]
  refine ⟨by rw [hfs, hsum], 0, by omega, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := Fin.ext (by simpa using hi)
    subst hi0
    simp only [fullState, Fin.val_zero, if_true]
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ _)
  · intro i hi
    have : (i : ℕ) ≠ 0 := by omega
    simp only [fullState, this, if_false]
    exact hnn i
