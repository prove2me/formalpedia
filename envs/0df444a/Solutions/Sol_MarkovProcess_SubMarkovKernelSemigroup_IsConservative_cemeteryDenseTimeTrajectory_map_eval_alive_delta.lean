-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.cemeteryDenseTimeTrajectory_map_eval_alive_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:14:44.428342+00:00
-- url     : https://prove2.me/submissions/60d5a901-6c75-43d3-b44e-bddff1424eed

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_denseTimeTrajectory_map_eval

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
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal



variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) (x : alpha) :
    ((denseTimeTrajectory P.cemeterySemigroup P.isConservative_cemeterySemigroup e iota).map
        (fun path ↦ path d)) (Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [denseTimeTrajectory_map_eval]
  rw [cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  rw [hP (iota d) x, tsub_self]
