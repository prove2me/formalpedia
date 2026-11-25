-- Prove2me | solution 1 for MeasureTheory.mulL2_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:19.123389+00:00
-- url     : https://prove2.me/submissions/4de4b9ab-619b-4b72-ab5d-fce95c8c1ffe

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Definitions.Def_BasicResults_Spectral_MultiplicationOperator

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal
open MeasureTheory
open MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
namespace MeasureTheory
theorem _root_.solution (f : α → 𝕜) (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    ⇑(mulL2 f hf g) =ᵐ[μ] f • ⇑g := by
  filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 2) (hf.toLp f) g,
    MemLp.coeFn_toLp hf] with x h1 h2
  simp [mulL2, h1, h2]
end MeasureTheory
