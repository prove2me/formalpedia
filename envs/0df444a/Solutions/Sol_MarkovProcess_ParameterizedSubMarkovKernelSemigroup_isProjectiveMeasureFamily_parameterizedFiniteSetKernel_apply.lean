-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:26:53.205409+00:00
-- url     : https://prove2.me/submissions/b3259f8b-4324-4a98-84bb-358e51779034

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeKernel_da0af7ef
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]













end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

open MeasureTheory ProbabilityTheory


variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]











namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
private theorem p2m_inline_parameterizedFiniteSetKernel_map_restrict_two
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    P.parameterizedFiniteSetKernel J =
      (P.parameterizedFiniteSetKernel I).map
        (Finset.restrict₂ (π := fun _ ↦ alpha) hJI) := by
  apply Kernel.ext
  intro q
  obtain ⟨theta, x⟩ := q
  rw [Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI),
    parameterizedFiniteSetKernel_apply, parameterizedFiniteSetKernel_apply]
  have h := congrArg (fun K : Kernel alpha (J → alpha) ↦ K x)
    ((hP theta).finiteSetKernel_map_restrict₂
      (P.toSubMarkovKernelSemigroup theta) hJI)
  change (P.toSubMarkovKernelSemigroup theta).finiteSetKernel J x =
    ((P.toSubMarkovKernelSemigroup theta).finiteSetKernel I).map
      (Finset.restrict₂ (π := fun _ ↦ alpha) hJI) x at h
  rw [Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI)] at h
  exact h

theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (theta : Theta) (x : alpha) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal ↦ alpha)
      (fun I : Finset NNReal ↦ P.parameterizedFiniteSetKernel I (theta, x)) := by
  intro I J hJI
  change P.parameterizedFiniteSetKernel J (theta, x) =
    Measure.map (Finset.restrict₂ (π := fun _ ↦ alpha) hJI)
      (P.parameterizedFiniteSetKernel I (theta, x))
  rw [← Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI)]
  exact congrArg (fun K : Kernel (Theta × alpha) (J → alpha) ↦ K (theta, x))
    (p2m_inline_parameterizedFiniteSetKernel_map_restrict_two P hP hJI)
