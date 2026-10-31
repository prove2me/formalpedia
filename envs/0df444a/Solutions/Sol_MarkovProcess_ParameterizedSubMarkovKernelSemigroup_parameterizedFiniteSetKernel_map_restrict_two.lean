-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteSetKernel_map_restrict_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:14:02.333144+00:00
-- url     : https://prove2.me/submissions/e7133010-6e39-451c-8b78-752eea80392a

import Mathlib
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
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open MarkovProcess MarkovProcess.ParameterizedSubMarkovKernelSemigroup
variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

theorem solution
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
