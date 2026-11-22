-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_norm_rpow_div_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:23.702778+00:00
-- url     : https://prove2.me/submissions/7d2d62e8-3621-4b84-9d75-df85b996c1be

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
open scoped RealInnerProductSpace
open MeasureTheory
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {α : ℝ} (hα : 0 < α)
    {u : Ω → E} {p : ℝ} (hup : MemLp u ↱p μ) :
    MemLp (‖u ·‖ ^ α) ↱(p / α) μ := by
  convert hup.norm_rpow_div ↱α using 1
  · simp [ENNReal.toReal_ofReal hα.le]
  · rw [ENNReal.ofReal_div_of_pos hα]
end NemytskiiLebesgue
