-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_iff_measurable_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:23.247957+00:00
-- url     : https://prove2.me/submissions/fafe3c71-2618-4c8e-bdf2-fa03ffd47741

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
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [ENorm E]
    {μ : Measure Ω} {p : ℝ≥0∞} {f : Ω → E} :
    MemLp f p μ ↔ AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ⊤ :=
  Iff.rfl
end NemytskiiLebesgue
