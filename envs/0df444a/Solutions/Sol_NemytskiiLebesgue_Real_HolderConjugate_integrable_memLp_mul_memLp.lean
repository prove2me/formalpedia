-- Prove2me | solution 1 for NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_mul_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:57.08601+00:00
-- url     : https://prove2.me/submissions/8a353984-3597-4ebb-b99f-1ecfa045b35c

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
namespace Real.HolderConjugate
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → ℝ} (hgq : MemLp g ↱q μ)
    {l : Ω → ℝ} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => g ω * l ω) μ := by
  convert! hgq.integrable_mul hlp
  exact hpq.symm.ennrealOfReal
end Real.HolderConjugate
end NemytskiiLebesgue
