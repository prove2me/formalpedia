-- Prove2me | solution 1 for NemytskiiLebesgue.ofReal_div_ofReal_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:28.80633+00:00
-- url     : https://prove2.me/submissions/fa521e97-e64f-4a43-a624-da2a227c1f19

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
theorem _root_.solution {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (↱p / ↱q).toReal = p / q := by
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
end NemytskiiLebesgue
