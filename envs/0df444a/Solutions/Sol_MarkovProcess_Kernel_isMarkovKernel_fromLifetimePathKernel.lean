-- Prove2me | solution 1 for MarkovProcess.Kernel.isMarkovKernel_fromLifetimePathKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:23.54925+00:00
-- url     : https://prove2.me/submissions/b4660600-c029-4514-a6c3-312d837dba6f

import Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
import Definitions.Def_MarkovProcess_V3H_Lifetime_NonexplosiveTransport_b1c8e8b2
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting nonexplosive lifetime laws to continuous paths

This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
ordinary continuous paths, independent of the off-support default.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]









section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]



end Measurable
end LifetimePath

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]













end Kernel
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting nonexplosive lifetime laws to continuous paths

This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
ordinary continuous paths, independent of the off-support default.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal





variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]





namespace MarkovProcess.Kernel

end MarkovProcess.Kernel
open MarkovProcess.Kernel
theorem solution
    (kappa : Kernel beta (LifetimePath alpha)) [IsMarkovKernel kappa]
    (default : ContinuousPath alpha) :
    IsMarkovKernel (fromLifetimePathKernel kappa default) := by
  rw [fromLifetimePathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (LifetimePath.measurable_continuousPathExtension default)
