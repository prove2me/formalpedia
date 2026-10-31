-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:14:44.993574+00:00
-- url     : https://prove2.me/submissions/08737d1a-ae7d-4414-84e3-d12367f08ae5

import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimeTrajectory_map_prefix
import Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_toSubMarkovKernelSemigroup_apply
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_denseTimeTrajectory_map_eval

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-time marginals of parameterized dense-time trajectories

This file identifies every coordinate marginal of the jointly measurable parameterized
trajectory kernel.  No standard-Borel assumption is imposed on the parameter space.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]



end
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
# One-time marginals of parameterized dense-time trajectories

This file identifies every coordinate marginal of the jointly measurable parameterized
trajectory kernel.  No standard-Borel assumption is imposed on the parameter space.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map (fun path ↦ path d) =
      P.parameterStateKernel (iota d) := by
  let k : ℕ := e.symm d
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : e i = d := by
    change e (e.symm d) = d
    exact e.apply_symm_apply d
  have hfun :
      (fun path : Fin (k + 1) → alpha ↦ path i) ∘
          SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e (k + 1) =
        fun path : D → alpha ↦ path d := by
    funext path
    change path (e i) = path d
    rw [hcoord]
  rw [← hfun, Kernel.map_comp_right]
  · rw [P.parameterizedDenseTimeTrajectory_map_prefix hP e iota (k + 1)]
    apply Kernel.ext
    rintro ⟨theta, x⟩
    rw [Kernel.map_apply _ (measurable_pi_apply i),
      parameterizedDenseTimePrefixKernel_apply, parameterStateKernel_apply]
    let Q := P.toSubMarkovKernelSemigroup theta
    have hmarg :=
      SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_eval
        Q (hP theta) e iota d
    rw [← hfun, Kernel.map_comp_right] at hmarg
    · rw [SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix] at hmarg
      have hx := congrArg (fun K : Kernel alpha alpha ↦ K x) hmarg
      change ((Q.denseTimePrefixKernel e iota (k + 1)).map
        (fun path ↦ path i)) x = Q (iota d) x at hx
      rw [Kernel.map_apply _ (measurable_pi_apply i)] at hx
      simpa only [Q, toSubMarkovKernelSemigroup_apply] using hx
    · exact
        SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e (k + 1)
    · exact measurable_pi_apply i
  · exact
      SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e (k + 1)
  · exact measurable_pi_apply i
