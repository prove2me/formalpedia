-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.jointKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:43:15.743113+00:00
-- url     : https://prove2.me/submissions/e8c222d5-67e6-441e-a306-be5b15d2aca7

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution (p : NNReal × α) : P.jointKernel p = P p.1 p.2 := rfl
