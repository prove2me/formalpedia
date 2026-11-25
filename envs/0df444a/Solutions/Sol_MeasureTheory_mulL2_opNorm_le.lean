-- Prove2me | solution 1 for MeasureTheory.mulL2_opNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:22.610659+00:00
-- url     : https://prove2.me/submissions/2c3c6109-e306-4ad5-ab7d-6ded0937ad6d

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
theorem _root_.solution (f : α → 𝕜) (hf : MemLp f ⊤ μ) :
    ‖mulL2 f hf‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  calc ‖mulL2 f hf‖
      ≤ ‖(ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ⊤ 2 2‖ * ‖hf.toLp f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖hf.toLp f‖ := by
        gcongr
        exact (ContinuousLinearMap.norm_holderL_le _).trans (ContinuousLinearMap.opNorm_mul_le _ _)
    _ = (eLpNorm f ⊤ μ).toReal := by rw [one_mul, Lp.norm_toLp]
end MeasureTheory
