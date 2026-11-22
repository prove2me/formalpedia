-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_le_eLpNorm_of_ae_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:04.988378+00:00
-- url     : https://prove2.me/submissions/077ac135-6616-4053-8ffc-3dda5472f793

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
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_eq_eLpNorm
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_mono_ae

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
    (hg : AEStronglyMeasurable g μ) (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ‖g ω‖) :
    integralLpNorm f p μ ≤ eLpNorm g p μ :=
  (integralLpNorm_mono_ae hfg).trans_eq (integralLpNorm_eq_eLpNorm hg)
end NemytskiiLebesgue
