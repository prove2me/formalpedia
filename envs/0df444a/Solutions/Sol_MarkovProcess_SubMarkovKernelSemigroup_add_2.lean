-- Prove2me | solution 2 for MarkovProcess.SubMarkovKernelSemigroup.add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:24:17.445502+00:00
-- url     : https://prove2.me/submissions/87866d80-cc0d-44d0-8862-6163d0067692

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution (s t : NNReal) : P (s + t) = (P t).comp (P s) :=
  P.kernel_add s t
