-- Prove2me | solution 1 for Komlos.spencer_six_deviations_small
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:50:48.877719+00:00
-- url     : https://prove2.me/submissions/18f6600a-48ff-492b-83fe-88221e36514b

import Mathlib
import Definitions.Def_Komlos_model

open Komlos in
theorem solution (n : ℕ) (hn : n ≤ 36) (A : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro i
  -- the signed row sum is just the row sum
  have hrow : ∑ j, A i j * (1 : ℝ) = ∑ j, A i j := by
    simp
  rw [hrow]
  -- each entry lies in [0,1]
  have hlb : (0:ℝ) ≤ ∑ j, A i j :=
    Finset.sum_nonneg fun j _ => by rcases h01 i j with h | h <;> simp [h]
  have hub : ∑ j, A i j ≤ (n : ℝ) := by
    calc ∑ j, A i j ≤ ∑ _j : Fin n, (1:ℝ) :=
          Finset.sum_le_sum fun j _ => by rcases h01 i j with h | h <;> simp [h]
      _ = (n : ℝ) := by simp
  rw [abs_of_nonneg hlb]
  -- n ≤ 6 * sqrt n for n ≤ 36
  have hs : Real.sqrt n ≤ 6 := by
    have : Real.sqrt (n : ℝ) ≤ Real.sqrt 36 := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hn
    calc Real.sqrt (n:ℝ) ≤ Real.sqrt 36 := this
      _ = 6 := by
          rw [show (36:ℝ) = 6^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 6)]
  have hsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hnn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  nlinarith [hub, hs, hsq, hnn]
