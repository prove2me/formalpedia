-- Prove2me | solution 1 for NemytskiiLebesgue.posPart_sub_posPart_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:47.385122+00:00
-- url     : https://prove2.me/submissions/0bf9c318-dcf7-4e27-9c02-05e6fc229c20

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
namespace NemytskiiLebesgue
theorem _root_.solution (x y : ℝ) : (x⁺ - y⁺) ^ 2 ≤ (x - y) ^ 2 := by
  cases le_total x 0 <;>
  cases le_total y 0 <;>
  simp [*] <;>
  nlinarith
end NemytskiiLebesgue
