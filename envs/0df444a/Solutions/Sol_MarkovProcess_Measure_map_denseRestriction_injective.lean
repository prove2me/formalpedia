-- Prove2me | solution 1 for MarkovProcess.Measure.map_denseRestriction_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:55:14.72819+00:00
-- url     : https://prove2.me/submissions/8ebb8185-9c3e-4edc-a45d-1f5c1443a0fc

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
theorem solution :
    Function.Injective
      (fun mu : MeasureTheory.Measure (ContinuousPath alpha) ↦
        mu.map ContinuousPath.denseRestriction) := by
  intro mu nu h
  ext s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hmap := congrArg
    (fun rho : MeasureTheory.Measure (DenseTime → alpha) ↦
      rho (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hmap
  rw [MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage,
    MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage] at hmap
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hmap
