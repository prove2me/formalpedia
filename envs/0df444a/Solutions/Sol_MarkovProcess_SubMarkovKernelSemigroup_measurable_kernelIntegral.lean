-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.measurable_kernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:45:29.041802+00:00
-- url     : https://prove2.me/submissions/653e11e4-d417-45bb-87d5-b81854fd453b

import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution {f : α → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 :=
  (hf.stronglyMeasurable.integral_kernel (κ := P.jointKernel)).measurable
