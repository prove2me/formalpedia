-- Prove2me | solution 1 for NemytskiiLebesgue.rpow_le_ofReal_rpow_of_le_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:46.253943+00:00
-- url     : https://prove2.me/submissions/a4a89414-139d-4c17-909e-e3bd1304bbcf

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
theorem _root_.solution
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    {x : ℝ≥0∞} (hx : x ≤ ↱R) :
    x ^ α ≤ ↱(R ^ α) := by
  convert ENNReal.rpow_le_rpow hx hα using 1
  rw [ENNReal.ofReal_rpow_of_pos hR]
end NemytskiiLebesgue
