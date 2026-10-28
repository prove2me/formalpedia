-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.ext
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:23:28.728497+00:00
-- url     : https://prove2.me/submissions/f26c4da8-21b2-473d-92b6-c45b6c9830a6

import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
theorem solution {P Q : SubMarkovKernelSemigroup α}
    (h : ∀ t, P t = Q t) : P = Q := by
  cases P; cases Q
  congr
  funext t
  exact h t
