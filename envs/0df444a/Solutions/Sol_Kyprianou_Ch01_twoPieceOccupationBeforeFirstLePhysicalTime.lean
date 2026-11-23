-- Prove2me | solution 1 for Kyprianou.Ch01.twoPieceOccupationBeforeFirstLePhysicalTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:46:50.643783+00:00
-- url     : https://prove2.me/submissions/750b7124-3e17-495e-a2e2-0913558f5ffe

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
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    ∀ u : ℝ≥0, (u : ℝ) < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞) := by
  intro u hu
  have hConst (v : ℝ≥0) (hv : v ≤ u) : X v ω = (y : ℤ) :=
    hPrefix v (lt_of_le_of_lt (NNReal.coe_le_coe.mpr hv) hu)
  have hJ :=
    Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula
      X ω y u hConst
  have huReal : (u : ℝ) ≤ (y : ℝ) * (t : ℝ) :=
    (le_of_lt hu).trans hFirst
  have huNN : u ≤ (y : ℝ≥0) * t := by
    apply NNReal.coe_le_coe.mp
    simpa using huReal
  have huENN : (u : ℝ≥0∞) ≤ (y : ℝ≥0∞) * (t : ℝ≥0∞) := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using (ENNReal.coe_le_coe.mpr huNN)
  have hy0 : (y : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hyTop : (y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top y
  calc
    reciprocalOccupation X u ω = (y : ℝ≥0∞)⁻¹ * (u : ℝ≥0∞) := hJ
    _ ≤ (y : ℝ≥0∞)⁻¹ * ((y : ℝ≥0∞) * (t : ℝ≥0∞)) :=
      mul_le_mul_of_nonneg_left huENN (by positivity)
    _ = (t : ℝ≥0∞) := ENNReal.inv_mul_cancel_left hy0 hyTop
