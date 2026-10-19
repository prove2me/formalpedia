-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_volume_le_expanded_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:44:59.433095+00:00
-- url     : https://prove2.me/submissions/02f9ec36-1009-476c-beef-6bdf3b20d1a1

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    (MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)})).toReal ≤
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i}).toReal := by
  have hsub :
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)}) ⊆
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i} := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ha, hxbox⟩
    have hcoord : ∀ i, 0 ≤ x i := by
      intro i
      exact (mul_nonneg (le_of_lt (hw i)) (Nat.cast_nonneg (a i))).trans (hxbox i).1
    have hsum : (∑ i : Fin m, x i) ≤ T + ∑ i : Fin m, w i := by
      calc
        (∑ i : Fin m, x i) ≤ ∑ i : Fin m, w i * ((a i : ℝ) + 1) :=
          Finset.sum_le_sum fun i _ => le_of_lt (hxbox i).2
        _ = (∑ i : Fin m, w i * (a i : ℝ)) + ∑ i : Fin m, w i := by
          calc
            (∑ i : Fin m, w i * ((a i : ℝ) + 1)) =
                ∑ i : Fin m, (w i * (a i : ℝ) + w i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (∑ i : Fin m, w i * (a i : ℝ)) + ∑ i : Fin m, w i :=
              Finset.sum_add_distrib
        _ ≤ T + ∑ i : Fin m, w i := add_le_add (hs a ha) (le_refl _)
    exact ⟨hcoord, hsum⟩
  have hbounded :
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i} ⊆
      Set.Icc (fun _ : Fin m => (0 : ℝ))
        (fun _ : Fin m => T + ∑ i : Fin m, w i) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro i
    exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2
  have hfinite :
      MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i} ≠ ⊤ := by
    exact ne_of_lt ((MeasureTheory.measure_mono hbounded).trans_lt
      isCompact_Icc.measure_lt_top)
  exact ENNReal.toReal_mono hfinite (MeasureTheory.measure_mono hsub)
