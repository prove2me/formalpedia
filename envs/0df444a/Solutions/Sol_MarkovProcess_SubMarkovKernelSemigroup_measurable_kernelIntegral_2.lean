-- Prove2me | solution 2 for MarkovProcess.SubMarkovKernelSemigroup.measurable_kernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:45:51.569791+00:00
-- url     : https://prove2.me/submissions/dd8dfe03-c20f-443a-9de7-d71acffd49f3

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_kernelIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem solution {f : α → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 :=
  (P.stronglyMeasurable_kernelIntegral hf.stronglyMeasurable).measurable
