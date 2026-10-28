-- Prove2me | solution 2 for MarkovProcess.SubMarkovKernelSemigroup.jointKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:43:47.206018+00:00
-- url     : https://prove2.me/submissions/38d73d98-d876-4000-8131-9368030c4c50

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem solution (p : NNReal × α) : P.jointKernel p = P p.1 p.2 :=
  rfl
