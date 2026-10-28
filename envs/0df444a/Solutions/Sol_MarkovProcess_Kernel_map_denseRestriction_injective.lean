-- Prove2me | solution 1 for MarkovProcess.Kernel.map_denseRestriction_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:23:04.293337+00:00
-- url     : https://prove2.me/submissions/f2ab0f8a-b1bc-4aef-89f9-3909a334d383

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
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


noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]




theorem solution :
    Function.Injective
      (fun kappa : Kernel beta (ContinuousPath alpha) ↦
        kappa.map ContinuousPath.denseRestriction) := by
  intro kappa eta h
  ext x s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hx := congrArg
    (fun z : Kernel beta (DenseTime → alpha) ↦
      z x (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hx
  rw [Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage,
    Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage] at hx
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hx
