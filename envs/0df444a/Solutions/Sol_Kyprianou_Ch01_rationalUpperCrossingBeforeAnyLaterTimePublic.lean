-- Prove2me | solution 1 for Kyprianou.Ch01.rationalUpperCrossingBeforeAnyLaterTimePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:46:44.709589+00:00
-- url     : https://prove2.me/submissions/e17d77da-469d-4cf7-a24e-affdd884414b

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_iff_rationalApproachingCrossings
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A time later than a continuous first passage contains a positive rational crossing. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω))
    (t : ℝ≥0)
    (ht : firstUpperPassage X s ω < (t : WithTop ℝ≥0)) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧
      Real.toNNReal (r : ℝ) < t ∧
      s < X (Real.toNNReal (r : ℝ)) ω := by
  classical
  letI : MeasurableSpace Ω := ⊥
  by_cases hex : ∃ u : ℝ≥0, 0 < u ∧ s < X u ω
  · let u : ℝ≥0 := sInf {v : ℝ≥0 | 0 < v ∧ s < X v ω}
    have hpass : firstUpperPassage X s ω = (u : WithTop ℝ≥0) := by
      simp [firstUpperPassage, hex, u] <;> rfl
    have hut : u < t := by
      exact WithTop.coe_lt_coe.mp (by simpa [hpass] using ht)
    have heps : 0 < t - u := tsub_pos_of_lt hut
    have hpassu : firstUpperPassage X s ω ≤ (u : WithTop ℝ≥0) := by
      rw [hpass]
    obtain ⟨r, hr, hrbound, hval⟩ :=
      (firstUpperPassage_le_iff_rationalApproachingCrossings
        X ω hContinuous s u).mp hpassu (t - u) heps
    refine ⟨r, hr, ?_, hval⟩
    have hreal : ((Real.toNNReal (r : ℝ)) : ℝ) = (r : ℝ) := by
      simp [Real.coe_toNNReal, hr.le]
    have heq : u + (t - u) = t := add_tsub_cancel_of_le hut.le
    have hrt : (r : ℝ) < (t : ℝ) := by
      simpa only [heq] using hrbound
    exact NNReal.coe_lt_coe.mp (by simpa only [hreal] using hrt)
  · have hpass : firstUpperPassage X s ω = ⊤ := by
      simp [firstUpperPassage, hex]
    rw [hpass] at ht
    exact False.elim (not_top_lt ht)
