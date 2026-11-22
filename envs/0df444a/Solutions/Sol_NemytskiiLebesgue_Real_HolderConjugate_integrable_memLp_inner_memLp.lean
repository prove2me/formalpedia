-- Prove2me | solution 1 for NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_inner_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:08.382568+00:00
-- url     : https://prove2.me/submissions/6dcb5ac3-4c63-4dc9-95fe-a97a375e38e4

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
public import Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_mul_memLp

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
namespace Real.HolderConjugate
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → E} (hgq : MemLp g ↱q μ)
    {l : Ω → E} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => ⟪g ω, l ω⟫) μ := by
  apply (Real.HolderConjugate.integrable_memLp_mul_memLp hpq hgq.norm hlp.norm).mono'
    (hgq.aestronglyMeasurable.inner hlp.aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm (g ω) (l ω)
end Real.HolderConjugate
end NemytskiiLebesgue
