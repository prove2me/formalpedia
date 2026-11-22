-- Prove2me | solution 1 for NemytskiiLebesgue.natCast_div_natCast_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:02.422352+00:00
-- url     : https://prove2.me/submissions/2e944d0c-1eac-4e93-ab6c-54037fab1927

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution (p : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (p : ℝ≥0∞) / (q : ℝ≥0∞) = ↱((p : ℝ) / (q : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos]
  · rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · positivity
end NemytskiiLebesgue
