-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_canonicalDiscreteLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:23:31.726343+00:00
-- url     : https://prove2.me/submissions/72aaaf44-ec53-425a-950c-36d22de77218

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









/-- The ordered-grid trajectory kernel is a Markov kernel. -/
theorem IsConservative.isMarkovKernel_orderedGridTrajectoryKernel
    (hP : P.IsConservative) (grid : OrderedGrid) :
    IsMarkovKernel (orderedGridTrajectoryKernel P hP grid) := by
  let (n : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid n) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid n
  rw [orderedGridTrajectoryKernel]
  infer_instance



/-- The ordered-grid trajectory law is a probability measure. -/
theorem IsConservative.isProbabilityMeasure_orderedGridTrajectoryLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    IsProbabilityMeasure (orderedGridTrajectoryLaw P hP grid x) := by
  let : IsMarkovKernel (orderedGridTrajectoryKernel P hP grid) :=
    IsConservative.isMarkovKernel_orderedGridTrajectoryKernel P hP grid
  exact IsMarkovKernel.isProbabilityMeasure x





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
    IsProbabilityMeasure (canonicalDiscreteLaw P hP grid x) := by
  exact IsConservative.isProbabilityMeasure_orderedGridTrajectoryLaw P hP grid x
