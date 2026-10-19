-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_ennreal_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:52:26.858126+00:00
-- url     : https://prove2.me/submissions/3bb0af60-22ec-4dff-a4ca-55bfd5bb88f8

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) :
    MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)}) =
      ∑ a ∈ s, ∏ i : Fin m, ENNReal.ofReal (w i) := by
  classical
  let B : (Fin m → ℕ) → Set (Fin m → ℝ) := fun a =>
    {x | ∀ i, w i * (a i : ℝ) ≤ x i ∧
      x i < w i * ((a i : ℝ) + 1)}
  have hbox (a : Fin m → ℕ) :
      B a = Set.pi Set.univ
        (fun i => Set.Ico (w i * (a i : ℝ))
          (w i * ((a i : ℝ) + 1))) := by
    ext x
    simp only [B, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Ico]
  have hmeas (a : Fin m → ℕ) : MeasurableSet (B a) := by
    rw [hbox a]
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)
  have hvol (a : Fin m → ℕ) :
      MeasureTheory.volume (B a) =
        ∏ i : Fin m, ENNReal.ofReal (w i) := by
    rw [hbox a, MeasureTheory.volume_pi_pi]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.volume_Ico]
    congr 1
    ring
  have hdisj : Set.PairwiseDisjoint (s : Set (Fin m → ℕ)) B := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    change (∀ i, w i * (a i : ℝ) ≤ x i ∧
      x i < w i * ((a i : ℝ) + 1)) at hxa
    change (∀ i, w i * (b i : ℝ) ≤ x i ∧
      x i < w i * ((b i : ℝ) + 1)) at hxb
    apply hab
    funext i
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (a i : ℝ) + 1 ≤ (b i : ℝ) := by
        rw [← Nat.cast_add_one]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hlt)
      have hmul := mul_le_mul_of_nonneg_left hcast (le_of_lt (hw i))
      exact (not_lt_of_ge (hmul.trans (hxb i).1)) (hxa i).2
    · have hcast : (b i : ℝ) + 1 ≤ (a i : ℝ) := by
        rw [← Nat.cast_add_one]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hgt)
      have hmul := mul_le_mul_of_nonneg_left hcast (le_of_lt (hw i))
      exact (not_lt_of_ge (hmul.trans (hxa i).1)) (hxb i).2
  change MeasureTheory.volume (⋃ a ∈ (s : Set (Fin m → ℕ)), B a) = _
  calc
    MeasureTheory.volume (⋃ a ∈ (s : Set (Fin m → ℕ)), B a) =
        ∑ a ∈ s, MeasureTheory.volume (B a) := by
      simpa only [Finset.mem_coe] using
        (MeasureTheory.measure_biUnion_finset
          (μ := MeasureTheory.volume) (s := s) (f := B)
          hdisj (fun a ha => hmeas a))
    _ = ∑ a ∈ s, ∏ i : Fin m, ENNReal.ofReal (w i) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hvol a
