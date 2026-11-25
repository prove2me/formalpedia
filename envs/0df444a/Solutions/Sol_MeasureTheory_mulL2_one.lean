-- Prove2me | solution 1 for MeasureTheory.mulL2_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:27.650116+00:00
-- url     : https://prove2.me/submissions/12fef622-98ab-404c-adb7-fa4d756296c8

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Definitions.Def_BasicResults_Spectral_MultiplicationOperator
public import Theorems.Thm_MeasureTheory_mulL2_coeFn

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal
open MeasureTheory
open MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
namespace MeasureTheory
theorem _root_.solution (h1 : MemLp (1 : α → 𝕜) ⊤ μ) :
    mulL2 (1 : α → 𝕜) h1 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ) := by
  refine ContinuousLinearMap.ext fun x => Lp.ext ?_
  filter_upwards [mulL2_coeFn (1 : α → 𝕜) h1 x] with a ha
  rw [ha]
  simp only [Pi.smul_apply', Pi.one_apply, one_smul, ContinuousLinearMap.id_apply]
end MeasureTheory
