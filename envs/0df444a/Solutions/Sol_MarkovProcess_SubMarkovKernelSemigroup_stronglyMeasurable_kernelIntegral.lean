-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_kernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:43:19.038647+00:00
-- url     : https://prove2.me/submissions/6e44fdd2-92fd-49f9-a3e4-2e49fa70f853

import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 :=
  hf.integral_kernel (κ := P.jointKernel)
