-- Prove2me | solution 1 for KSATSingleFlip.Connect.count_mixture_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:52.403537+00:00
-- url     : https://prove2.me/submissions/8dd9cc39-a09b-4044-9bf7-c916279fee4c

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (E B : Set Ω) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (p : ℝ≥0∞)
    (hfiber : ∀ j : ℕ, μ ((E \ B) ∩ N ⁻¹' {j}) ≤ μ (N ⁻¹' {j})*p) :
    μ E ≤ p + μ B := by
  classical
  let A : ℕ → Set Ω := fun j => (E \ B) ∩ N ⁻¹' {j}
  let C : ℕ → Set Ω := fun j => N ⁻¹' {j}
  have hA (j : ℕ) : MeasurableSet (A j) := (hE.diff hB).inter (hN (measurableSet_singleton j))
  have hC (j : ℕ) : MeasurableSet (C j) := hN (measurableSet_singleton j)
  have hdisA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hi : N x = i := by simpa [A] using hx.2
    have hj : N x = j := by simpa [A] using hy.2
    exact hij (hi.symm.trans hj)
  have hdisC : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hi : N x = i := by simpa [C] using hx
    have hj : N x = j := by simpa [C] using hy
    exact hij (hi.symm.trans hj)
  have hunionA : (⋃ j, A j) = E \ B := by
    ext x
    simp only [Set.mem_iUnion, A, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j,h,_⟩; exact h
    · intro hx; exact ⟨N x,hx,rfl⟩
  have hunionC : (⋃ j, C j) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, C, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨N x,rfl⟩
  have hc : (∑' j, μ (C j)) = 1 := by
    rw [← measure_iUnion hdisC hC, hunionC, measure_univ]
  have ha : μ (E \ B) ≤ p := by
    rw [← hunionA, measure_iUnion hdisA hA]
    calc
      (∑' j, μ (A j)) ≤ ∑' j, μ (C j)*p := ENNReal.tsum_le_tsum hfiber
      _ = (∑' j, μ (C j))*p := ENNReal.tsum_mul_right
      _ = p := by rw [hc, one_mul]
  calc
    μ E ≤ μ ((E \ B) ∪ B) := measure_mono (by intro x hx; by_cases hb : x ∈ B <;> simp [hx,hb])
    _ ≤ μ (E \ B) + μ B := measure_union_le _ _
    _ ≤ p + μ B := by gcongr
