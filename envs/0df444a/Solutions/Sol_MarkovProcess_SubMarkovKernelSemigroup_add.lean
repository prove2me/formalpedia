-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:23:53.811203+00:00
-- url     : https://prove2.me/submissions/759bc7d5-4423-42f4-a27e-b004c89f85d7

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem solution (s t : NNReal) : P (s + t) = (P t).comp (P s) :=
  P.kernel_add s t
