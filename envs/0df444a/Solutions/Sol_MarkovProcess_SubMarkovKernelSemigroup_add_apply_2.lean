-- Prove2me | solution 2 for MarkovProcess.SubMarkovKernelSemigroup.add_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:31:20.917087+00:00
-- url     : https://prove2.me/submissions/da115ce7-4cfb-4668-b44b-05f1cf52658a

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem solution (s t : NNReal) (x : α) :
    P (s + t) x = (P s x).bind (P t) := by
  rw [P.add, Kernel.comp_apply]
