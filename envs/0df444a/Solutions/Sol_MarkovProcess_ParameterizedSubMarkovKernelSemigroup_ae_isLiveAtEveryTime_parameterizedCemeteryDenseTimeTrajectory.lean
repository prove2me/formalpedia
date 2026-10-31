-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:19:31.955599+00:00
-- url     : https://prove2.me/submissions/27c1b816-8f15-4a89-aff5-832a5369534b

import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_Parameterized_CemeteryDenseTimeSupport_55332836
import Definitions.Def_MarkovProcess_V3H_Parameterized_CemeterySemigroup_9e5cada4
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
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.Constructions.SumProd
import Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimeTrajectory_map_eval

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*}









namespace Kernel

variable [MeasurableSpace α]











/-- The mass assigned to the cemetery singleton is exactly the missing mass. -/
theorem cemeteryExtension_alive_singleton_delta (κ : ProbabilityTheory.Kernel α α) (x : α) :
    cemeteryExtension κ (Cemetery.alive x) {Cemetery.delta} = 1 - κ x Set.univ := by
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery α)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr : MeasurableSet (Set.range (Sum.inr : Unit → α ⊕ Unit)))
  rw [cemeteryExtension_alive_apply' κ x hdelta]
  have hpre : Cemetery.alive ⁻¹' ({Cemetery.delta} : Set (Cemetery α)) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Sum.inl_ne_inr, Set.notMem_empty]
  rw [hpre, measure_empty]
  simp only [Set.indicator_of_mem, Set.mem_singleton_iff, Pi.one_apply, mul_one, zero_add]











end Kernel

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized cemetery-extension semigroups

This file extends a jointly measurable family of sub-Markov semigroups by one absorbing
cemetery state.  The construction is jointly measurable in the parameter, time, and state.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

/-- Evaluation of the parameterized cemetery extension is ordinary cemetery extension of the
corresponding parameter and time slice. -/
@[simp]
theorem cemeterySemigroup_apply (theta : Theta) (t : NNReal) :
    P.cemeterySemigroup theta t = Kernel.cemeteryExtension (P theta t) := rfl





end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery marginals of parameterized dense-time trajectories

This file proves a one-time marginal identity.  It makes no simultaneous path-support or
lifetime claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

/-- From a live starting state, every coordinate of the parameterized cemetery trajectory has
zero cemetery mass when the original parameter slices are conservative. -/
theorem parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) (d : D) :
    ((P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota).map
      (fun path ↦ path d)) (theta, Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [parameterizedDenseTimeTrajectory_map_eval, parameterStateKernel_apply,
    cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  have hmass := hP theta (iota d) x
  change P theta (iota d) x Set.univ = 1 at hmass
  rw [hmass]
  exact tsub_self 1

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section



namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]



end ParameterizedSubMarkovKernelSemigroup

end
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory






variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    ∀ᵐ path ∂P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x),
      IsLiveAtEveryTime path := by
  let mu := P.cemeterySemigroup.parameterizedDenseTimeTrajectory
    P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x)
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery alpha)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr :
        MeasurableSet (Set.range (Sum.inr : Unit → alpha ⊕ Unit)))
  have hcoordinate : ∀ n : ℕ, ∀ᵐ path ∂mu, path (e n) ≠ Cemetery.delta := by
    intro n
    have hzero :=
      P.parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
        hP e iota theta x (e n)
    rw [Kernel.map_apply _ (measurable_pi_apply (e n)),
      Measure.map_apply (measurable_pi_apply (e n)) hdelta] at hzero
    rw [ae_iff]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, not_ne_iff] using! hzero
  filter_upwards [ae_all_iff.mpr hcoordinate] with path hpath
  intro d
  simpa only [e.apply_symm_apply] using hpath (e.symm d)
