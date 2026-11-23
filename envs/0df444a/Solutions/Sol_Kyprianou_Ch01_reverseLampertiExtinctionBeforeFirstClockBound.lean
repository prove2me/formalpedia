-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiExtinctionBeforeFirstClockBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:55:18.118079+00:00
-- url     : https://prove2.me/submissions/40762178-53ff-47c8-885c-187e0ca8d08e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixOccupationFormula
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a : ℝ) (ha : 0 < a)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a → X u ω = (y : ℤ))
    (hFirst : a ≤ (y : ℝ) * (t : ℝ)) :
    ∀ u : ℝ≥0, (u : ℝ) < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞) := by
  intro u hu
  have hP : ∀ v : ℝ≥0, v ≤ u → X v ω = (y : ℤ) := by
    intro v hv
    exact hPrefix v (lt_of_le_of_lt (NNReal.coe_le_coe.mpr hv) hu)
  have hNN : u ≤ (y : ℝ≥0) * t := by
    apply NNReal.coe_le_coe.mp
    calc
      (u : ℝ) ≤ a := hu.le
      _ ≤ (y : ℝ) * (t : ℝ) := hFirst
      _ = (((y : ℝ≥0) * t : ℝ≥0) : ℝ) := by simp
  have hBound : (u : ℝ≥0∞) ≤ (y : ℝ≥0∞) * (t : ℝ≥0∞) := by
    exact_mod_cast hNN
  have hy0 : (y : ℝ≥0∞) ≠ 0 := by
    simp [Nat.ne_of_gt hy]
  have hyFin : (y : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    reciprocalOccupation X u ω = (y : ℝ≥0∞)⁻¹ * (u : ℝ≥0∞) :=
      Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula X ω y u hP
    _ ≤ (y : ℝ≥0∞)⁻¹ * ((y : ℝ≥0∞) * (t : ℝ≥0∞)) :=
      by gcongr
    _ = (t : ℝ≥0∞) := ENNReal.inv_mul_cancel_left hy0 hyFin
