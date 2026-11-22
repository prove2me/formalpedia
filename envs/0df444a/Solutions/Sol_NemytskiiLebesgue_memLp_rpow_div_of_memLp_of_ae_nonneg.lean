-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_rpow_div_of_memLp_of_ae_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:56.58417+00:00
-- url     : https://prove2.me/submissions/c3256c75-9389-438c-8cd9-f84df407d9bd

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
public import Theorems.Thm_NemytskiiLebesgue_memLp_norm_rpow_div_of_memLp

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
    {α : ℝ} (hα : 0 < α)
    {v : Ω → ℝ} (h0v : 0 ≤ᵐ[μ] v) {p : ℝ} (hvp : MemLp v ↱p μ) :
    MemLp (v · ^ α) ↱(p / α) μ := by
  apply (memLp_norm_rpow_div_of_memLp hα hvp).ae_eq
  filter_upwards [h0v] with ω hω
  rw [Real.norm_of_nonneg hω]
end NemytskiiLebesgue
