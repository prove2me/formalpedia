-- Prove2me | solution 2 for MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:38:41.084198+00:00
-- url     : https://prove2.me/submissions/2f8ffa77-9778-4653-8f16-819352b73342

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}
theorem solution (κ : Kernel α β) [IsMarkovKernel κ] : IsSubMarkovKernel κ :=
  fun x => by simp
