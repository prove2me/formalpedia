-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.measure_le_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:18:20.995307+00:00
-- url     : https://prove2.me/submissions/3219ccc6-37ed-4c20-9255-28a1d3a1741e

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}
theorem solution (hκ : IsSubMarkovKernel κ) (x : α) (s : Set β) : κ x s ≤ 1 :=
  (measure_mono (Set.subset_univ s)).trans (hκ x)
