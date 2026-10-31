-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.continuous_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:57:20.270811+00:00
-- url     : https://prove2.me/submissions/870941f1-e7cf-4648-8f44-765b0250c1e8

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Semigroup.StronglyContinuousContractionSemigroup

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]





end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution
    (S : StronglyContinuousContractionSemigroup E) :
    Continuous fun tf : NNReal × E ↦ S tf.1 tf.2 := by
  rw [continuous_iff_continuousAt]
  intro tf
  exact S.p2m_embedded_0957dd8f4e4395ee continuousAt_fst continuousAt_snd
