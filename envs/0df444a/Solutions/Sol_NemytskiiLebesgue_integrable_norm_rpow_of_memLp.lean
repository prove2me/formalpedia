-- Prove2me | solution 1 for NemytskiiLebesgue.integrable_norm_rpow_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:53.717883+00:00
-- url     : https://prove2.me/submissions/5951ec1b-292f-48c0-8ab3-13fb3fe455db

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
    {p : ℝ} (hp : 1 < p)
    {u : Ω → E} (hup : MemLp u ↱p μ) :
    Integrable (‖u ·‖ ^ p) μ := by
  convert hup.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.← (zero_lt_one.trans hp)))
  simp [ENNReal.toReal_ofReal (zero_le_one.trans hp.le)]
end NemytskiiLebesgue
