-- Prove2me | solution 1 for MeasureTheory.mulL2_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:32.086065+00:00
-- url     : https://prove2.me/submissions/2f05e1cf-c29f-404e-8b4c-de45b9a11c16

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
theorem _root_.solution (f : α → 𝕜) (hf : MemLp f ⊤ μ)
    (hreal : ∀ᵐ a ∂μ, (starRingEnd 𝕜) (f a) = f a) :
    IsSelfAdjoint (mulL2 f hf) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn f hf x, mulL2_coeFn f hf y, hreal] with a hx hy hr
  rw [hx, hy]
  simp only [Pi.smul_apply']
  rw [inner_smul_left, inner_smul_right, hr]
end MeasureTheory
