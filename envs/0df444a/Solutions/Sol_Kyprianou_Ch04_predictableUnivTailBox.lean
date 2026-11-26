-- Prove2me | solution 1 for Kyprianou.Ch04.predictableUnivTailBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:50.168961+00:00
-- url     : https://prove2.me/submissions/edf2d28c-abb1-4eed-b529-22f65fdb0eb1

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- The universal generator restricts to the positive-time band. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
 (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.univ : Set ((NNReal × Omega) × ℝ))).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  classical
  refine ⟨0, B, fun _ => c, bot_le, hB, Set.Subset.rfl,
    stronglyMeasurable_const, fun _ => le_rfl, ?_⟩
  intro w z hz
  by_cases h : z ∈ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  · have h' : z.1 ∈ Set.Ioc (0 : ℝ) (t : ℝ) := by
      exact ⟨lt_of_le_of_ne h.1.1 (Ne.symm hz), h.1.2⟩
    have h'' : z ∈ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B := ⟨h', h.2⟩
    simp [Set.indicator_of_mem h, Set.indicator_of_mem h'']
  · have h' : z ∉ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B := fun hz' => h ⟨⟨hz'.1.1.le,hz'.1.2⟩,hz'.2⟩
    simp [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
