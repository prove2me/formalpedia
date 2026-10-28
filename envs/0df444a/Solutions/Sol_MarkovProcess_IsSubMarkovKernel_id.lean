-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:38:27.502196+00:00
-- url     : https://prove2.me/submissions/00662ca1-5a6c-43bd-990d-dc41d125ac5d

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

theorem solution : IsSubMarkovKernel (Kernel.id : Kernel α α) := by
  intro x
  rw [Kernel.id_apply]
  exact le_of_eq measure_univ
