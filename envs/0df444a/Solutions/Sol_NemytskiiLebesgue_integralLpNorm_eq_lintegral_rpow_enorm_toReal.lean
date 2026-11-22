-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_eq_lintegral_rpow_enorm_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:26.262006+00:00
-- url     : https://prove2.me/submissions/30216a73-0af1-4c84-a7f2-f390ba347625

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
    (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    integralLpNorm f p μ = (∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  simp only [integralLpNorm, hp, hp', ↓reduceIte, eLpNorm']
end NemytskiiLebesgue
