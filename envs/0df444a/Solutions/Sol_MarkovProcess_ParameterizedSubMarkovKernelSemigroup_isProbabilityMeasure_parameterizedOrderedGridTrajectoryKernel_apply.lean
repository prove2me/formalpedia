-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProbabilityMeasure_parameterizedOrderedGridTrajectoryKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:04:48.537414+00:00
-- url     : https://prove2.me/submissions/5e37aa8c-4090-4f98-91b7-4e3f3d1cb050

import Definitions.Def_MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized trajectory laws on a fixed ordered time grid

This file constructs a jointly measurable kernel from a parameter and starting state to the
discrete trajectory on one fixed ordered grid. The parameter is carried as a deterministic
component of an augmented state through the Ionescu--Tulcea construction, then removed from the
output path.

The result is a path-law kernel on `Theta × alpha` with values in measures on `ℕ → alpha`.
It is not a continuous-time path law and does not assert measurability in the grid.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

















/-- The parameterized ordered-grid trajectory kernel is a Markov kernel. -/
theorem isMarkovKernel_parameterizedOrderedGridTrajectoryKernel
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (grid : OrderedGrid) :
    IsMarkovKernel (P.parameterizedOrderedGridTrajectoryKernel hP grid) := by
  let (n : ℕ) : IsMarkovKernel (P.parameterizedOrderedGridStepKernel grid n) :=
    P.isMarkovKernel_parameterizedOrderedGridStepKernel hP grid n
  rw [parameterizedOrderedGridTrajectoryKernel]
  apply Kernel.IsMarkovKernel.map
  exact measurable_pi_iff.mpr fun n ↦ measurable_snd.comp (measurable_pi_apply n)



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
# Parameterized trajectory laws on a fixed ordered time grid

This file constructs a jointly measurable kernel from a parameter and starting state to the
discrete trajectory on one fixed ordered grid. The parameter is carried as a deterministic
component of an augmented state through the Ionescu--Tulcea construction, then removed from the
output path.

The result is a path-law kernel on `Theta × alpha` with values in measures on `ℕ → alpha`.
It is not a continuous-time path law and does not assert measurability in the grid.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory



variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)



















namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (grid : OrderedGrid) (theta : Theta) (x : alpha) :
    IsProbabilityMeasure (P.parameterizedOrderedGridTrajectoryKernel hP grid (theta, x)) := by
  let : IsMarkovKernel (P.parameterizedOrderedGridTrajectoryKernel hP grid) :=
    P.isMarkovKernel_parameterizedOrderedGridTrajectoryKernel hP grid
  exact IsMarkovKernel.isProbabilityMeasure (theta, x)
