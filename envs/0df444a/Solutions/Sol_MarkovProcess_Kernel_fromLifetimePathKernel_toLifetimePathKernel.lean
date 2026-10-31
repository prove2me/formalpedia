-- Prove2me | solution 1 for MarkovProcess.Kernel.fromLifetimePathKernel_toLifetimePathKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:15.056754+00:00
-- url     : https://prove2.me/submissions/fdcd7d66-08d9-4c89-beb2-60abe09e2d5f

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
@[simp]
theorem solution
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    fromLifetimePathKernel (toLifetimePathKernel kappa) default = kappa := by
  rw [fromLifetimePathKernel_eq_map, toLifetimePathKernel_eq_map, ← Kernel.map_comp_right]
  · have hcomp : LifetimePath.continuousPathExtension default ∘
        LifetimePath.ofContinuousPath = id := by
      funext eta
      exact LifetimePath.continuousPathExtension_ofContinuousPath default eta
    rw [hcomp, Kernel.map_id]
  · exact LifetimePath.measurable_ofContinuousPath
  · exact LifetimePath.measurable_continuousPathExtension default
