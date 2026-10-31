-- Prove2me | solution 1 for MarkovProcess.Measure.map_denseRestriction_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:10.168682+00:00
-- url     : https://prove2.me/submissions/cdc184ad-d590-4897-a7ee-83ad8978fe36

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_MeasureIdentification_8dc880ce
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MarkovProcess_Measure_map_denseRestriction_injective

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]





end
end Measure
end MarkovProcess


open MarkovProcess
open MarkovProcess.Measure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory



variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



namespace MarkovProcess.Measure

end MarkovProcess.Measure
open MarkovProcess.Measure
theorem solution
    {mu nu : MeasureTheory.Measure (ContinuousPath alpha)} :
    mu.map ContinuousPath.denseRestriction = nu.map ContinuousPath.denseRestriction ↔
      mu = nu := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) h
  · intro h
    exact congrArg
      (fun rho : MeasureTheory.Measure (ContinuousPath alpha) ↦
        rho.map ContinuousPath.denseRestriction) h
