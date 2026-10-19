-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_radius
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:01:31.443011+00:00
-- url     : https://prove2.me/submissions/64705263-ad24-4594-95b9-7498b84d9c90

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (0 : ℝ)}) =
    (0 : ℝ) ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have hsub : {x : Fin (n + 1) → ℝ |
          (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (0 : ℝ)} ⊆
          {x : Fin (n + 1) → ℝ | x 0 = 0} := by
        intro x hx
        have hle : x 0 ≤ ∑ i : Fin (n + 1), x i :=
          Finset.single_le_sum (f := fun i : Fin (n + 1) => x i)
            (fun i hi => hx.1 i) (Finset.mem_univ 0)
        exact le_antisymm (hle.trans hx.2) (hx.1 0)
      have hhyper : MeasureTheory.volume
          {x : Fin (n + 1) → ℝ | x 0 = 0} = 0 := by
        simpa only [MeasureTheory.volume_pi] using
          (MeasureTheory.Measure.pi_hyperplane
            (fun _ : Fin (n + 1) => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            0 0)
      have hzero : MeasureTheory.volume
          {x : Fin (n + 1) → ℝ |
            (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (0 : ℝ)} = 0 :=
        MeasureTheory.measure_mono_null hsub hhyper
      simp [hzero]
