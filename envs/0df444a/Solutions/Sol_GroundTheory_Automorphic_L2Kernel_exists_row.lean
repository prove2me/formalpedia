-- Prove2me | solution 1 for GroundTheory.Automorphic.L2Kernel.exists_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:02.111699+00:00
-- url     : https://prove2.me/submissions/25a26a38-4e20-45e3-836f-d4620c9d3f1e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.L2Kernel
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]
variable (k : Lp 𝕜 2 (μ.prod ν))
namespace GroundTheory.Automorphic.L2Kernel
theorem _root_.solution {x : X} (hx : ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞) :
    ∃ h : Lp 𝕜 2 ν, ‖h‖ₑ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∧
      ∀ f : Lp 𝕜 2 ν, kernelFun (ν := ν) k f x = ⟪h, f⟫_𝕜 := by
  have hconj : ∀ y, ‖conj (k (x, y))‖ₑ = ‖k (x, y)‖ₑ := fun y => by
    rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]
  have hm : MemLp (fun y => conj (k (x, y))) 2 ν := by
    refine ⟨(RCLike.continuous_conj.comp_aestronglyMeasurable
      (measurable_row k x).aestronglyMeasurable), lt_top_of_sq_lt_top ?_⟩
    rw [eLpNorm_two_sq]
    simpa only [hconj] using hx
  refine ⟨hm.toLp _, ?_, fun f => ?_⟩
  · rw [Lp.enorm_def, eLpNorm_congr_ae hm.coeFn_toLp, eLpNorm_two_sq]
    simp only [hconj]
  · rw [MeasureTheory.L2.inner_def, kernelFun]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with y hy
    rw [RCLike.inner_apply, hy, RCLike.conj_conj, mul_comm]
end GroundTheory.Automorphic.L2Kernel
