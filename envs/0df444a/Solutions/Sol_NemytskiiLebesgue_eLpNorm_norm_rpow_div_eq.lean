-- Prove2me | solution 1 for NemytskiiLebesgue.eLpNorm_norm_rpow_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:53.220086+00:00
-- url     : https://prove2.me/submissions/8405e716-27b1-403e-911b-018cc52807ac

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
    {D : Type*} [NormedAddCommGroup D] (u : Ω → D)
    (hu : AEStronglyMeasurable u μ) {p α : ℝ} (hα : 0 < α) (hp : 0 < p) :
    eLpNorm (‖u ·‖ ^ α) ↱(p / α) μ = (eLpNorm u ↱p μ) ^ α := by
  rw [eLpNorm_norm_rpow u hα]
  rw [←ENNReal.ofReal_mul, div_mul_cancel₀ _ hα.ne']
  positivity
end NemytskiiLebesgue
