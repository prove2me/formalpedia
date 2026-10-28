-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.bound_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:38:15.361162+00:00
-- url     : https://prove2.me/submissions/0ddea9b0-0cde-478b-8dd4-9df449e66ad9

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

theorem solution (hκ : IsSubMarkovKernel κ) : κ.bound ≤ 1 := by
  apply iSup_le
  exact hκ
