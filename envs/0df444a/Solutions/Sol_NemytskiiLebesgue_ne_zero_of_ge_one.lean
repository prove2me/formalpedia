-- Prove2me | solution 1 for NemytskiiLebesgue.ne_zero_of_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:22.332969+00:00
-- url     : https://prove2.me/submissions/13b11827-1aa6-4126-b9bf-fff04ce13380

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
theorem _root_.solution {α : Type*} [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1
  : α)]
    {x : α} (h1x : 1 ≤ x) : x ≠ 0 := by
  intro hx0
  rw [hx0] at h1x
  exact one_ne_zero (le_antisymm h1x zero_le_one)
end NemytskiiLebesgue
