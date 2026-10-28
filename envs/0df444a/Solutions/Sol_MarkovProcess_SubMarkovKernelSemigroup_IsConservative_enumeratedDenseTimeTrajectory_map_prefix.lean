-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.enumeratedDenseTimeTrajectory_map_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:40:05.297181+00:00
-- url     : https://prove2.me/submissions/9cf7f415-faeb-4174-b2a6-9b515b6e2fc1

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_partialTraj_map_denseTimeHistoryMeasurableEquiv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for finite dense-time histories

This file augments finite prefix laws by their starting point and disintegrates the joint law of
a prefix and its next observation. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]



/-- Mapping an augmented history back to its two components recovers its defining product law. -/
theorem augmentedPrefixKernel_map_historyEquiv (P : SubMarkovKernelSemigroup α)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (augmentedPrefixKernel P e ι n).map (DenseTimeHistory.historyEquiv n) =
      Kernel.id ×ₖ denseTimePrefixKernel P e ι n := by
  rw [augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
  · have hcomp :
        (DenseTimeHistory.historyEquiv n : DenseTimeHistory α n →
            α × (Fin n → α)) ∘
            (DenseTimeHistory.historyEquiv n).symm = id := by
      funext z
      exact MeasurableEquiv.apply_symm_apply _ z
    rw [hcomp, Kernel.map_id]
  · exact (DenseTimeHistory.historyEquiv n).symm.measurable
  · exact (DenseTimeHistory.historyEquiv n).measurable
end
end SubMarkovKernelSemigroup
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

open MeasureTheory ProbabilityTheory


noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

























/-- Before dropping the initial coordinate, every finite marginal of the trajectory is the
corresponding `partialTraj`, started from the deterministic time-zero history. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.trajDenseStep_map_frestrictLe (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    ((Kernel.traj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0).comap
        initialTrajHistory measurable_initialTrajHistory).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
        initialTrajHistoryKernel := by
  rw [← Kernel.comap_map_comm _ measurable_initialTrajHistory
    (Preorder.measurable_frestrictLe n), Kernel.traj_map_frestrictLe,
    ← Kernel.comp_deterministic_eq_comap]
  rfl













omit [StandardBorelSpace α] [Nonempty α] in
/-- Restriction to the first `n` enumeration coordinates is measurable. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measurable_enumeratedDenseTimePrefix (n : ℕ) :
    Measurable (enumeratedDenseTimePrefix (α := α) n) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (X := fun _ : ℕ ↦ α) i

omit [StandardBorelSpace α] [Nonempty α] in
private theorem enumeratedDenseTimePrefix_dropInitialTrajCoordinate (n : ℕ) :
    enumeratedDenseTimePrefix (α := α) n ∘ dropInitialTrajCoordinate =
      Prod.snd ∘ DenseTimeHistory.historyEquiv n ∘
        denseTimeHistoryMeasurableEquiv n ∘ Preorder.frestrictLe n := by
  funext path i
  rfl


theorem solution
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (enumeratedDenseTimeTrajectory P hP e ι).map
        (enumeratedDenseTimePrefix (α := α) n) =
      denseTimePrefixKernel P e ι n := by
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  rw [enumeratedDenseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [enumeratedDenseTimePrefix_dropInitialTrajCoordinate]
    rw [Kernel.map_comp_right]
    · rw [← Function.comp_assoc]
      rw [Kernel.map_comp_right _ (Preorder.measurable_frestrictLe n)
          ((DenseTimeHistory.historyEquiv n).measurable.comp
            (denseTimeHistoryMeasurableEquiv (α := α) n).measurable)]
      rw [trajDenseStep_map_frestrictLe]
      rw [Kernel.map_comp_right _
        (denseTimeHistoryMeasurableEquiv (α := α) n).measurable
        (DenseTimeHistory.historyEquiv n).measurable]
      rw [partialTraj_map_denseTimeHistoryMeasurableEquiv]
      rw [augmentedPrefixKernel_map_historyEquiv]
      rw [← Kernel.snd_eq, Kernel.snd_prod]
    · exact ((DenseTimeHistory.historyEquiv n).measurable.comp
        (denseTimeHistoryMeasurableEquiv (α := α) n).measurable).comp
          (Preorder.measurable_frestrictLe n)
    · exact measurable_snd
  · exact measurable_dropInitialTrajCoordinate
  · exact measurable_enumeratedDenseTimePrefix n
