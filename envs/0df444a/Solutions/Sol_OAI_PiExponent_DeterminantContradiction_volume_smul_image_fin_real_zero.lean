-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:53:45.99447+00:00
-- url     : https://prove2.me/submissions/44d4177f-848a-4512-9e27-efdf71f8b877

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution (m : ℕ) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal
        (MeasureTheory.volume ((fun x : Fin m → ℝ => (0 : ℝ) • x) '' s)) =
      (0 : ℝ) ^ m * ENNReal.toReal (MeasureTheory.volume s) := by
  cases m with
  | zero =>
      have hmap : (fun x : Fin 0 → ℝ => (0 : ℝ) • x) = id := by
        funext x i
        exact Fin.elim0 i
      rw [hmap, Set.image_id, pow_zero, one_mul]
  | succ m =>
      have hsub :
          ((fun x : Fin (m + 1) → ℝ => (0 : ℝ) • x) '' s) ⊆
            ({0} : Set (Fin (m + 1) → ℝ)) := by
        rintro y ⟨x, hx, rfl⟩
        simp
      have hzero :
          MeasureTheory.volume
              ((fun x : Fin (m + 1) → ℝ => (0 : ℝ) • x) '' s) = 0 :=
        MeasureTheory.measure_mono_null hsub (by simp)
      rw [hzero]
      simp only [ENNReal.toReal_zero, pow_succ, mul_zero, zero_mul]
