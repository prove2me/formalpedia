-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationPhysicalIntervalCut
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:16:12.770331+00:00
-- url     : https://prove2.me/submissions/c9ef94c2-1529-479e-a7cc-60a88ac72b3c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    reciprocalOccupation X u ω =
      reciprocalOccupation X (Real.toNNReal A) ω +
        (∫⁻ s in Set.Ioc A (u : ℝ),
          (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) := by
  classical
  have ha : ((Real.toNNReal A : ℝ≥0) : ℝ) = A :=
    Real.coe_toNNReal A hA
  have hUnion :
      Set.Ioc (0 : ℝ) (u : ℝ) =
        Set.Ioc (0 : ℝ) A ∪ Set.Ioc A (u : ℝ) := by
    ext s
    constructor
    · rintro ⟨h0, hsU⟩
      by_cases hSA : s ≤ A
      · exact Or.inl ⟨h0, hSA⟩
      · exact Or.inr ⟨lt_of_not_ge hSA, hsU⟩
    · intro h
      rcases h with h | h
      · exact ⟨h.1, h.2.trans hu⟩
      · exact ⟨lt_of_le_of_lt hA h.1, h.2⟩
  have hDisjoint :
      Disjoint (Set.Ioc (0 : ℝ) A) (Set.Ioc A (u : ℝ)) := by
    rw [Set.disjoint_left]
    intro s h1 h2
    exact (not_lt_of_ge h1.2) h2.1
  unfold reciprocalOccupation
  rw [ha, hUnion]
  exact MeasureTheory.lintegral_union measurableSet_Ioc hDisjoint
