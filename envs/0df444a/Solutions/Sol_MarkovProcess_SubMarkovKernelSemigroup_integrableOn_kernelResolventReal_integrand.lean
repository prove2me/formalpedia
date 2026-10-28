-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.integrableOn_kernelResolventReal_integrand
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:48:48.077462+00:00
-- url     : https://prove2.me/submissions/1fcec4d4-a526-4b77-8ccf-5093cc4eb96f

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_KernelResolvents
import Definitions.Def_MarkovProcess_JointKernel

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]
theorem kib_aux (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hfD x)
  have hle : (P t x) univ ≤ 1 := P.isSubMarkovKernel t x
  haveI : IsFiniteMeasure (P t x) := ⟨lt_of_le_of_lt hle ENNReal.one_lt_top⟩
  have h1 := norm_integral_le_of_norm_le_const (μ := P t x) (f := f) (C := D)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfD y)
  have h2 : (P t x).real univ ≤ 1 := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
  unfold kernelIntegral
  rw [← Real.norm_eq_abs]
  calc _ ≤ D * (P t x).real univ := h1
    _ ≤ D * 1 := by gcongr
    _ = D := mul_one D
theorem solution
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
  have hm : Measurable fun p : NNReal × alpha ↦ kernelIntegral (P p.1) f p.2 :=
    (hf.stronglyMeasurable.integral_kernel (κ := P.jointKernel)).measurable
  have hm2 : Measurable fun t : ℝ => kernelIntegral (P (Real.toNNReal t)) f x :=
    hm.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hint : IntegrableOn (fun t : ℝ => D * Real.exp (-lam * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul D
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hm2).aestronglyMeasurable
  · show ‖Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x‖ ≤ D * Real.exp (-lam * t)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (kib_aux P hfD _ x) (Real.exp_pos _).le
