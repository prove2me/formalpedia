-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.norm_kernelIntegral_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:44:09.738005+00:00
-- url     : https://prove2.me/submissions/c4b77611-46ae-43b5-9235-420682de48fd

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_KernelResolvents

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]
theorem solution (P : SubMarkovKernelSemigroup alpha)
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
