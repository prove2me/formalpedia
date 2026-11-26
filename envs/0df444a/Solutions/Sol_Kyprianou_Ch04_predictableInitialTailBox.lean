-- Prove2me | solution 1 for Kyprianou.Ch04.predictableInitialTailBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:50.95288+00:00
-- url     : https://prove2.me/submissions/3cb6a3e2-b337-4355-970f-d907583ee3a3

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- The time-zero generator vanishes away from time zero. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Omega) (C₀ : Set ℝ)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((({⊥} : Set NNReal) ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  classical
  refine ⟨0, ∅, fun _ => 0, bot_le, MeasurableSet.empty, Set.empty_subset _,
    stronglyMeasurable_const, fun _ => by simpa using abs_nonneg c, ?_⟩
  intro w z hz
  by_cases h : z ∈ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  · have hp : 0 < z.1 := lt_of_le_of_ne h.1.1 (Ne.symm hz)
    have hn : z.1.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hp)
    simp [Set.indicator_of_mem h, hn]
  · simp [Set.indicator_of_notMem h]
