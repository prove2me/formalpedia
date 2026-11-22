-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_eq_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:22.802771+00:00
-- url     : https://prove2.me/submissions/75255a3e-e2cd-4864-8fce-1943e76572d0

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
theorem _root_.solution {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {f : Ω → E} {p : ℝ≥0∞} {μ : Measure Ω}
    (hf : AEStronglyMeasurable f μ) : integralLpNorm f p μ = eLpNorm f p μ := by
  simp [integralLpNorm, eLpNorm, hf]
end NemytskiiLebesgue
