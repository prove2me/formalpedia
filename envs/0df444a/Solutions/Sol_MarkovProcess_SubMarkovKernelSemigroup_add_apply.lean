-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.add_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:30:40.960515+00:00
-- url     : https://prove2.me/submissions/721fca89-27f7-4a9b-add5-5c0c73dfacc6

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution (s t : NNReal) (x : α) :
    P (s + t) x = (P s x).bind (P t) := by
  change P.kernel (s + t) x = (P.kernel s x).bind (P.kernel t)
  rw [P.kernel_add, Kernel.comp_apply]
