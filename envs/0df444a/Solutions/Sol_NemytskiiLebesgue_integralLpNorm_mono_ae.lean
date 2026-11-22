-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_mono_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:26.743186+00:00
-- url     : https://prove2.me/submissions/82e48258-88b2-4f19-835b-b54005417a80

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
theorem _root_.solution {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : Ω → E} {g : Ω → F} {p : ℝ≥0∞} {μ : Measure Ω}
    (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ‖g ω‖) : integralLpNorm f p μ ≤ integralLpNorm g p μ := by
  unfold integralLpNorm
  split_ifs
  · rfl
  · apply eLpNormEssSup_mono_enorm_ae
    exact hfg.mono fun _ h => by
      simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal h
  · exact eLpNorm'_mono_ae ENNReal.toReal_nonneg hfg
end NemytskiiLebesgue
