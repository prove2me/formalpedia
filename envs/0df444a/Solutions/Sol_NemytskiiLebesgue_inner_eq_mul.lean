-- Prove2me | solution 1 for NemytskiiLebesgue.inner_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:49.49211+00:00
-- url     : https://prove2.me/submissions/af726549-cb01-47ef-88e8-709fc55db31f

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
namespace NemytskiiLebesgue
theorem _root_.solution (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [RCLike.inner_apply']
  norm_num
end NemytskiiLebesgue
