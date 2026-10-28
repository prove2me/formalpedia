-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:38:33.668848+00:00
-- url     : https://prove2.me/submissions/8be4e09c-e0d8-4997-837e-19731b119d40

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

theorem solution (κ : Kernel α β) [IsMarkovKernel κ] : IsSubMarkovKernel κ := by
  intro x
  exact le_of_eq measure_univ
