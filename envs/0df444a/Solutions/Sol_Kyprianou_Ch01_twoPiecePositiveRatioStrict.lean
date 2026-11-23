-- Prove2me | solution 1 for Kyprianou.Ch01.twoPiecePositiveRatioStrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:51:43.405986+00:00
-- url     : https://prove2.me/submissions/e7e545fa-8a0b-46a4-b40b-c0a667c4dd85

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
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
    0 < t →
    (t : ℝ≥0∞) <
      (1 / ((y + j - 1 : ℕ) : ℝ≥0∞)) *
        (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) := by
  intro ht
  let z : ℕ := y + j - 1
  have hzPos : 0 < z := hPost
  have hzNotZero : (z : ℝ≥0∞) ≠ 0 := by exact_mod_cast hzPos.ne'
  have hzNotTop : (z : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top z
  have htNotZero : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have htNotTop : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hNat : (z : ℝ≥0∞) < ((y + j : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (show z < y + j by omega)
  have hScaled :
      (z : ℝ≥0∞) * (t : ℝ≥0∞) <
        ((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞) :=
    ENNReal.mul_lt_mul_left htNotZero htNotTop hNat
  have hInv := ENNReal.mul_lt_mul_right
    (ENNReal.inv_ne_zero.mpr hzNotTop)
    (ENNReal.inv_ne_top.mpr hzNotZero) hScaled
  rw [ENNReal.inv_mul_cancel_left hzNotZero hzNotTop] at hInv
  simpa only [one_div, z] using hInv
