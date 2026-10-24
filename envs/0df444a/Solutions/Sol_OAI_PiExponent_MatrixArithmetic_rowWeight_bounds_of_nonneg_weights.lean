-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.rowWeight_bounds_of_nonneg_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:54:58.811991+00:00
-- url     : https://prove2.me/submissions/e73eafd8-cbaf-4237-9655-ff0c8a0abe9a

import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem solution
    (m K : ℕ) (v0 theta H : ℝ) (w : Fin m → ℝ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hw : ∀ i, 0 ≤ w i)
    (ρ : OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H) :
    0 ≤ ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * w i ∧
      (∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * w i) ≤ theta * H := by
  let a := ρ.2.1
  have hmem : a ∈ OAI.PiExponent.strictWeightedSimplex
      (OAI.PiExponent.InterpolationMatrix.rowWeights v0 theta w) H := ρ.2.2
  have hbudget : v0 * (a 0 : ℝ) +
      ∑ i : Fin m, (w i / theta) * (a i.succ : ℝ) < H := by
    have hstrict := hmem
    simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter] at hstrict
    simpa [OAI.PiExponent.InterpolationMatrix.rowWeights, Fin.sum_univ_succ]
      using hstrict.2
  have hnorm : 0 ≤ ∑ i : Fin m, (w i / theta) * (a i.succ : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (div_nonneg (hw i) (le_of_lt htheta)) (Nat.cast_nonneg _)
  have hzero : 0 ≤ v0 * (a 0 : ℝ) :=
    mul_nonneg (le_of_lt hv0) (Nat.cast_nonneg _)
  have hscale : theta *
      (∑ i : Fin m, (w i / theta) * (a i.succ : ℝ)) =
      ∑ i : Fin m, (a i.succ : ℝ) * w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    <;> ring
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) (hw i)
  · rw [← hscale]
    have hTle : (∑ i : Fin m, (w i / theta) * (a i.succ : ℝ)) ≤ H := by
      linarith
    exact mul_le_mul_of_nonneg_left hTle (le_of_lt htheta)
