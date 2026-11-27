-- Prove2me | solution 1 for GroundTheory.Automorphic.contKernelOp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:47.525533+00:00
-- url     : https://prove2.me/submissions/b4e6ca3e-0a97-4667-a2e7-12313e2ffb76

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTraceComp
import Theorems.Thm_GroundTheory_Automorphic_compKernel_apply
import Theorems.Thm_GroundTheory_Automorphic_contKernelOp_apply_ae


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace GroundTheory.Automorphic
theorem _root_.solution (a b : C(X × X, ℂ)) :
    (contKernelOp μ a).comp (contKernelOp μ b) = contKernelOp μ (compKernel μ a b) := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [contKernelOp_apply_ae μ a (contKernelOp μ b f),
    contKernelOp_apply_ae μ (compKernel μ a b) f] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  have h3 : (fun y => a (x, y) * contKernelOp μ b f y) =ᵐ[μ]
      fun y => ∫ z, a (x, y) * (b (y, z) * f z) ∂μ := by
    filter_upwards [contKernelOp_apply_ae μ b f] with y hy
    rw [hy, integral_const_mul]
  rw [integral_congr_ae h3]
  have hf : Integrable (fun z => f z) μ := (Lp.memLp f).integrable one_le_two
  have hab : Continuous fun p : X × X => a (x, p.1) * b (p.1, p.2) :=
    (a.continuous.comp (continuous_const.prodMk continuous_fst)).mul b.continuous
  have hint : Integrable (Function.uncurry fun y z => a (x, y) * (b (y, z) * f z)) (μ.prod μ) := by
    have h1 : Integrable (fun p : X × X => (1 : ℂ) * f p.2) (μ.prod μ) :=
      (integrable_const (1 : ℂ)).mul_prod hf
    have h2 := h1.bdd_mul (c := ‖a‖ * ‖b‖)
      (measurable_of_continuous_compactProd hab).aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [norm_mul]
        exact mul_le_mul (a.norm_coe_le_norm _) (b.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _))
    refine h2.congr (ae_of_all _ fun p => ?_)
    obtain ⟨y, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [compKernel_apply]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  ring
end GroundTheory.Automorphic
