-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_twoStepProduct_c0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:57:19.201952+00:00
-- url     : https://prove2.me/submissions/0d0a87b6-78a9-4918-b0f3-051f3dc93fb4

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

/-- Feller continuity permits both the time and the `C₀` integrand to vary. -/
theorem IsFellerKernelSemigroup.tendsto_kernelIntegral_c0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {t : X → NNReal} {t₀ : NNReal}
    {f : X → C₀(alpha, ℝ)} {f₀ : C₀(alpha, ℝ)}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral (P (t a)) (f a) x) l
      (nhds (kernelIntegral (P t₀) f₀ x)) := by
  have haction := hP.c0Semigroup.p2m_embedded_0957dd8f4e4395ee ht hf
  have heval : Continuous fun g : C₀(alpha, ℝ) ↦ g x :=
    (ZeroAtInftyContinuousMap.isometry_toBCF (α := alpha) (β := ℝ)).continuous.eval
      continuous_const
  simpa only [IsFellerKernelSemigroup.c0Semigroup_apply_apply] using!
    heval.continuousAt.tendsto.comp haction



end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
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




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X}
    {t s : X → NNReal} {t₀ s₀ : NNReal}
    {f g : X → C₀(alpha, ℝ)} {f₀ g₀ : C₀(alpha, ℝ)}
    (ht : Tendsto t l (nhds t₀)) (hs : Tendsto s l (nhds s₀))
    (hf : Tendsto f l (nhds f₀)) (hg : Tendsto g l (nhds g₀)) (x : alpha) :
    Tendsto
      (fun a ↦ kernelIntegral (P (t a))
        (f a * hP.c0Semigroup (s a) (g a)) x)
      l
      (nhds (kernelIntegral (P t₀)
        (f₀ * hP.c0Semigroup s₀ g₀) x)) := by
  have hinner : Tendsto (fun a ↦ hP.c0Semigroup (s a) (g a)) l
      (nhds (hP.c0Semigroup s₀ g₀)) :=
    hP.c0Semigroup.p2m_embedded_0957dd8f4e4395ee hs hg
  exact hP.tendsto_kernelIntegral_c0 ht (hf.mul hinner) x
