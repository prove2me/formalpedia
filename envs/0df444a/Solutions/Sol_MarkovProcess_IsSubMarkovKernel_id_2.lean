-- Prove2me | solution 2 for MarkovProcess.IsSubMarkovKernel.id
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:38:44.815309+00:00
-- url     : https://prove2.me/submissions/18e22f01-a4c2-41c4-878d-d0e1887b7343

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}
theorem solution : IsSubMarkovKernel (Kernel.id : Kernel α α) :=
  fun x => by simp
