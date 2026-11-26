-- Prove2me | solution 1 for Kyprianou.Ch04.predictableBeyondHorizonTailBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:50.439226+00:00
-- url     : https://prove2.me/submissions/2acb9939-041a-4178-83b2-3a633e961741

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A tail starting after the horizon has zero restricted contribution. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (a₀ : NNReal) (A : Set Omega) (C₀ : Set ℝ) (hat : ¬ a₀ ≤ t)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.Ioi a₀ ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  classical
  refine ⟨t, ∅, fun _ => 0, le_rfl, MeasurableSet.empty, Set.empty_subset _,
    stronglyMeasurable_const, fun _ => by simpa using abs_nonneg c, ?_⟩
  intro w z hz
  by_cases hu : z ∈ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  · have hco : (z.1.toNNReal : ℝ) = z.1 := Real.coe_toNNReal _ hu.1.1
    have hn : ¬ a₀ < z.1.toNNReal := by
      rw [← NNReal.coe_lt_coe, hco]
      exact not_lt_of_ge (hu.1.2.trans (by exact_mod_cast le_of_lt (lt_of_not_ge hat)))
    simp [Set.indicator_of_mem hu, hn]
  · simp [Set.indicator_of_notMem hu]
