-- Prove2me | solution 1 for MarkovProcess.Kernel.map_denseRestriction_map_continuousExtension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:54.463229+00:00
-- url     : https://prove2.me/submissions/2437c3fc-9d22-42f1-9549-2ab4381c0633

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]







end
end Kernel
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory



variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

namespace MarkovProcess.Kernel

end MarkovProcess.Kernel
open MarkovProcess.Kernel
@[simp]
theorem solution
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    (kappa.map ContinuousPath.denseRestriction).map
        (ContinuousPath.continuousExtension default) = kappa := by
  rw [← Kernel.map_comp_right]
  · have hcomp : ContinuousPath.continuousExtension default ∘
        ContinuousPath.denseRestriction = id := by
      funext omega
      exact ContinuousPath.continuousExtension_denseRestriction default omega
    rw [hcomp, Kernel.map_id]
  · exact ContinuousPath.measurable_denseRestriction
  · exact ContinuousPath.measurable_continuousExtension default
