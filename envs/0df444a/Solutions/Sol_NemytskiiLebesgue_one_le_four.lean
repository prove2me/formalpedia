-- Prove2me | solution 1 for NemytskiiLebesgue.one_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:45.736607+00:00
-- url     : https://prove2.me/submissions/3ca9f7ec-80df-4548-928f-e8a61bdd0891

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
theorem _root_.solution {α : Type*} [AddCommMonoidWithOne α] [Preorder α] [ZeroLEOneClass α] [AddLeftMono
  α] :
    (1 : α) ≤ (4 : α) :=
  calc (1 : α)
    = 1 + 0 := (add_zero 1).symm
  _ ≤ 1 + 3 := add_le_add_right zero_le_three 1
  _ = 4     := by norm_num
end NemytskiiLebesgue
