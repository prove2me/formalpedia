-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.isFiniteKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:18:27.039988+00:00
-- url     : https://prove2.me/submissions/c4a94795-2c88-47d0-9e10-265d0c1400cf

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}
theorem solution (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, hκ⟩⟩
