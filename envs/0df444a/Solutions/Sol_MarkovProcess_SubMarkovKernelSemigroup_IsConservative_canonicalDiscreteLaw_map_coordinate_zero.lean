-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.canonicalDiscreteLaw_map_coordinate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:19:51.198064+00:00
-- url     : https://prove2.me/submissions/18ec3814-906e-46a5-aba7-6f5e6a038af0

import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscreteLaw_ed3fbdc7
import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscretePath_a2b715fb
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Adapted

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


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete trajectory laws

This file equips the canonical discrete path space with the trajectory law of
a conservative transition-kernel semigroup along one fixed ordered grid.  It
records exact finite-prefix and coordinate marginal identities.  No
conditional-expectation Markov property is asserted here.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)





/-- Restricting the canonical law to coordinates through `n` gives the
corresponding finite Ionescu--Tulcea trajectory law. -/
theorem IsConservative.canonicalDiscreteLaw_map_prefix
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (canonicalDiscreteLaw P hP grid x).map
        (fun path : DiscretePath α => fun i : Finset.Iic n => path i) =
      Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x) := by
  exact IsConservative.orderedGridTrajectoryLaw_map_frestrictLe P hP grid x n

/-- The law of coordinate `n` is the last-coordinate pushforward of the
finite trajectory law through `n`. -/
theorem IsConservative.canonicalDiscreteLaw_map_coordinate
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (canonicalDiscreteLaw P hP grid x).map (DiscretePath.coordinate n) =
      (Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x)).map (fun history => history ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rw [← IsConservative.canonicalDiscreteLaw_map_prefix P hP grid x n,
    Measure.map_map]
  · rfl
  · exact measurable_pi_apply (X := fun _ : Finset.Iic n => α)
      ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  · exact measurable_pi_iff.mpr fun _ => DiscretePath.measurable_coordinate (α := α) _



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
# Canonical discrete trajectory laws

This file equips the canonical discrete path space with the trajectory law of
a conservative transition-kernel semigroup along one fixed ordered grid.  It
records exact finite-prefix and coordinate marginal identities.  No
conditional-expectation Markov property is asserted here.
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
    (canonicalDiscreteLaw P hP grid x).map (DiscretePath.coordinate 0) = Measure.dirac x := by
  rw [IsConservative.canonicalDiscreteLaw_map_coordinate P hP grid x 0,
    Kernel.partialTraj_self, Kernel.id_apply]
  exact Measure.map_dirac'
    (measurable_pi_apply (X := fun _ : Finset.Iic 0 => α)
      ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (initialHistory x)
