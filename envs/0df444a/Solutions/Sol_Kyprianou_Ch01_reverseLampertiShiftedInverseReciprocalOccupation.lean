-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiShiftedInverseReciprocalOccupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:03:58.094938+00:00
-- url     : https://prove2.me/submissions/751ce439-e129-4301-bb3d-a6b7011d2dfa

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_nonnegativeSInfTranslatedImage
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationStrictCrossingSetShift
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
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    inverseReciprocalOccupation X t ω =
      (((Real.toNNReal A : ℝ≥0) : WithTop ℝ≥0) +
        inverseReciprocalOccupation Y
          (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω) := by
  classical
  let a : ℝ≥0 := Real.toNNReal A
  let r : ℝ≥0 := Real.toNNReal ((t : ℝ) - A / (y : ℝ))
  let P : Set ℝ≥0 :=
    {u | (t : ℝ≥0∞) < reciprocalOccupation X u ω}
  let S : Set ℝ≥0 :=
    {v | (r : ℝ≥0∞) < reciprocalOccupation Y v ω}
  have hSet : P = (fun v : ℝ≥0 => a + v) '' S := by
    simpa [a, r, P, S] using
      reciprocalOccupationStrictCrossingSetShift
        X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative
  have hExists :
      (∃ u : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X u ω) ↔
      (∃ v : ℝ≥0, (r : ℝ≥0∞) < reciprocalOccupation Y v ω) := by
    constructor
    · rintro ⟨u, hu⟩
      have hh : u ∈ (fun v : ℝ≥0 => a + v) '' S := by
        rw [← hSet]
        exact hu
      rcases hh with ⟨v, hv, heq⟩
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      have hh : a + v ∈ P := by
        rw [hSet]
        exact ⟨v, hv, rfl⟩
      exact ⟨a + v, hh⟩
  change
    (if ∃ u : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X u ω
     then ((sInf P : ℝ≥0) : WithTop ℝ≥0) else ⊤) =
      ((a : WithTop ℝ≥0) +
        (if ∃ v : ℝ≥0, (r : ℝ≥0∞) < reciprocalOccupation Y v ω
         then ((sInf S : ℝ≥0) : WithTop ℝ≥0) else ⊤))
  by_cases hS : ∃ v : ℝ≥0, (r : ℝ≥0∞) < reciprocalOccupation Y v ω
  · have hX : ∃ u : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X u ω :=
      hExists.mpr hS
    have hSnonempty : S.Nonempty := hS
    simp only [if_pos hX, if_pos hS, hSet]
    rw [nonnegativeSInfTranslatedImage a S hSnonempty]
    exact (WithTop.coe_add a (sInf S)).symm
  · have hX : ¬ ∃ u : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X u ω :=
      fun hx => hS (hExists.mp hx)
    simp only [if_neg hX, if_neg hS, WithTop.add_top]
