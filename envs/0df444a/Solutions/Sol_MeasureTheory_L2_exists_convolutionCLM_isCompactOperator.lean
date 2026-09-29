-- Prove2me | solution 1 for MeasureTheory.L2.exists_convolutionCLM_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/58088348-e3e3-56fb-843f-bf18ebb6cb66

import Definitions.Def_Mathlib_MeasureTheory_Function_L2KernelOperator
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator

open scoped Convolution
open MeasureTheory ContinuousLinearMap

theorem solution
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T := by

  haveI : μ.Regular := inferInstance
  haveI : μ.IsNegInvariant := inferInstance
  haveI : MeasurableNeg G := ⟨continuous_neg.measurable⟩
  haveI : MeasurableAdd G :=
    ⟨fun c => (continuous_const.add continuous_id).measurable,
     fun c => (continuous_id.add continuous_const).measurable⟩

  have hKcont : Continuous fun p : G × G => (f : G → ℂ) (p.1 - p.2) :=
    f.continuous.comp (continuous_fst.sub continuous_snd)
  have hKsm : StronglyMeasurable fun p : G × G => (f : G → ℂ) (p.1 - p.2) :=
    HasCompactSupport.stronglyMeasurable_of_prod hKcont (HasCompactSupport.of_compactSpace _)
  have hKmem : MemLp (fun p : G × G => (f : G → ℂ) (p.1 - p.2)) 2 (μ.prod μ) :=
    MemLp.of_bound hKsm.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (p.1 - p.2))
  set K : Lp ℂ 2 (μ.prod μ) := hKmem.toLp _ with hK_def

  refine ⟨L2.kernelIntegralCLM K, fun φ => ?_, L2.isCompactOperator_kernelIntegralCLM K⟩

  refine (L2.kernelIntegralCLM_coeFn K φ).trans ?_

  have hstep1 : (fun x => ∫ y, (K : G × G → ℂ) (x, y) * (φ : G → ℂ) y ∂μ) =ᵐ[μ]
      (fun x => ∫ y, (f : G → ℂ) (x - y) * (φ : G → ℂ) y ∂μ) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hKmem.coeFn_toLp] with x hx
    exact integral_congr_ae (hx.mono fun y hy => congrArg (· * (φ : G → ℂ) y) hy)

  refine hstep1.trans (Filter.Eventually.of_forall fun x => ?_)
  exact (convolution_mul_swap (μ := μ) (f := (f : G → ℂ)) (g := (φ : G → ℂ)) (x := x)).symm

end S_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator
end P2MW
export P2MW.S_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator (solution)
