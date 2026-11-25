-- Prove2me | solution 1 for MeasureTheory.mulL2_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:25.619809+00:00
-- url     : https://prove2.me/submissions/ff89a96a-e928-4823-a78b-48fab0e985d0

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
theorem _root_.solution (f g : α → 𝕜) (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    (mulL2 f hf).comp (mulL2 g hg) = mulL2 (f * g) (memLp_mul_top hf hg) := by
  refine ContinuousLinearMap.ext fun x => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [mulL2_coeFn f hf (mulL2 g hg x), mulL2_coeFn g hg x,
    mulL2_coeFn (f * g) (memLp_mul_top hf hg) x] with a h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply', Pi.mul_apply, h2, mul_smul]
end MeasureTheory
