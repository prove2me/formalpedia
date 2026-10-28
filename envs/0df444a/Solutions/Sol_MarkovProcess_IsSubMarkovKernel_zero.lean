-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:38:21.455093+00:00
-- url     : https://prove2.me/submissions/bc533373-6d62-4e77-9b69-945d44003bf5

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}

theorem solution : IsSubMarkovKernel (0 : Kernel α β) := by
  intro x
  rw [zero_apply]
  exact zero_le
