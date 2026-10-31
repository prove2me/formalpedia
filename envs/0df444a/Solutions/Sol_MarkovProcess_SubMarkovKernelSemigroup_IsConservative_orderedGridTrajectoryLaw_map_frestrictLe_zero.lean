-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.orderedGridTrajectoryLaw_map_frestrictLe_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:32:40.956769+00:00
-- url     : https://prove2.me/submissions/6cd52a52-8990-467f-9302-d58b21168538

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]



namespace OrderedGrid



end OrderedGrid





namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)















/-- Every finite prefix of the ordered-grid law is the corresponding finite
Ionescu--Tulcea trajectory law. -/
theorem IsConservative.orderedGridTrajectoryLaw_map_frestrictLe
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (orderedGridTrajectoryLaw P hP grid x).map
        (fun path : ℕ → α => fun i : Finset.Iic n => path i) =
      Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x) := by
  let (k : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid k) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid k
  exact Kernel.traj_map_frestrictLe_apply
    (X := fun _ => α) (κ := orderedGridStepKernel P grid) 0 n (initialHistory x)



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
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

open MeasureTheory
open ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]









variable (P : SubMarkovKernelSemigroup α)

















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    (orderedGridTrajectoryLaw P hP grid x).map
        (fun path : ℕ → α => fun i : Finset.Iic 0 => path i) =
      Measure.dirac (initialHistory x) := by
  simpa only [Kernel.partialTraj_self, Kernel.id_apply] using
    IsConservative.orderedGridTrajectoryLaw_map_frestrictLe P hP grid x 0
