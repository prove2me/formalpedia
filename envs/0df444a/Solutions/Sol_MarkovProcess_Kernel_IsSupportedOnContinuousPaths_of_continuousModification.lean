-- Prove2me | solution 1 for MarkovProcess.Kernel.IsSupportedOnContinuousPaths.of_continuousModification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:12:28.698233+00:00
-- url     : https://prove2.me/submissions/db5b00bd-1e0a-4a80-8b75-eb6781253f27

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
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
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous support from a continuous modification

This file turns a continuous-time modification of the coordinate process of a dense-time law
into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
the simultaneous choice of all dense-time modification identities, which is valid because
`DenseTime` is countable.

The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
-/

open MeasureTheory ProbabilityTheory Set


noncomputable section


variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]


theorem solution
    (kappa : Kernel beta (DenseTime → alpha))
    (hmod : ∀ b, ∃ Y : NNReal → (DenseTime → alpha) → alpha,
      (∀ omega, Continuous (fun t ↦ Y t omega)) ∧
        ∀ q, (fun omega : DenseTime → alpha ↦ omega q) =ᵐ[kappa b]
          Y (DenseTime.castOrderEmbedding q)) :
    IsSupportedOnContinuousPaths kappa := by
  intro b
  obtain ⟨Y, hYcont, hYmod⟩ := hmod b
  have hmod_all : ∀ᵐ omega ∂kappa b, ∀ q,
      omega q = Y (DenseTime.castOrderEmbedding q) omega :=
    ae_all_iff.2 hYmod
  filter_upwards [hmod_all] with omega homega
  let path : ContinuousPath alpha :=
    ⟨fun t ↦ Y t omega, hYcont omega⟩
  refine ⟨path, ?_⟩
  funext q
  exact (homega q).symm
