-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:10:31.328873+00:00
-- url     : https://prove2.me/submissions/3c32a716-36ac-4839-9a01-92a8259d237e

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
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


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



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
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty


variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {l : Filter X} {times : X → FiniteOrderedTimes 1}
    {times0 : FiniteOrderedTimes 1}
    (ht : Tendsto (fun a ↦ times a 0) l (nhds (times0 0)))
    (f : C₀(alpha, ℝ)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral
        ((finiteTimeKernel P (times a)).map (fun path ↦ path 0)) f x)
      l (nhds (kernelIntegral
        ((finiteTimeKernel P times0).map (fun path ↦ path 0)) f x)) := by
  simp_rw [p2m_embedded_5bab9ee57d353238]
  exact hP.tendsto_kernelIntegral_c0 ht tendsto_const_nhds x
