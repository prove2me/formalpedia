-- Prove2me | solution 1 for GroundTheory.Automorphic.L2Kernel.hsNormSq_kernelOp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:30.308938+00:00
-- url     : https://prove2.me/submissions/a63f0535-7eb8-4ada-858f-bedbf8b24349

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_exists_row
import Theorems.Thm_GroundTheory_Automorphic_enorm_inner_comm
import Theorems.Thm_GroundTheory_Automorphic_enorm_sq_eq_tsum


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
theorem _root_.solution : hsNormSq (kernelOp k) ≤ ‖k‖ₑ ^ 2 := by
  let b := stdHilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [hsNormSq]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  calc ∑ i ∈ s, ‖kernelOp k (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ x, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        Finset.sum_congr rfl fun i _ => enorm_kernelOpₗ_sq k (b i)
    _ = ∫⁻ x, ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        (lintegral_finsetSum' s fun i _ =>
          ((aestronglyMeasurable_kernelFun k (b i)).enorm.pow_const 2)).symm
    _ ≤ ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_rowSq_lt_top k] with x hx
        obtain ⟨h, hh, hK⟩ := exists_row k hx
        calc ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2
            = ∑ i ∈ s, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 :=
              Finset.sum_congr rfl fun i _ => by rw [hK, enorm_inner_comm]
          _ ≤ ∑' i, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 := ENNReal.sum_le_tsum s
          _ = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν := by rw [← enorm_sq_eq_tsum b, hh]
    _ = ‖k‖ₑ ^ 2 := lintegral_rowSq k
end GroundTheory.Automorphic.L2Kernel
