-- Prove2me | solution 1 for MeasureTheory.Measure.ae_of_compProd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:31.29444+00:00
-- url     : https://prove2.me/submissions/1c315b5b-b66d-4f09-80c1-ea3e8762d4f2

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
namespace ProbabilityTheory.Kernel
namespace _root_.MeasureTheory.Measure
theorem _root_.solution {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : (μ ⊗ₘ κ) s = 0) :
    ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s) = 0 := by
  let t := toMeasurable (μ ⊗ₘ κ) s
  have ht : (μ ⊗ₘ κ) t = 0 := by
    unfold t
    rwa [measure_toMeasurable]
  rw [Measure.compProd_apply (measurableSet_toMeasurable _ _), lintegral_eq_zero_iff] at ht
  swap; · exact measurable_kernel_prodMk_left (measurableSet_toMeasurable _ _)
  filter_upwards [ht] with a ha
  exact measure_mono_null (fun y hy ↦ subset_toMeasurable (μ ⊗ₘ κ) s hy) ha
end _root_.MeasureTheory.Measure
end ProbabilityTheory.Kernel
