-- Prove2me | solution 1 for MarkovProcess.Kernel.IsSupportedOnContinuousPaths.toContinuousPathKernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:51:51.405245+00:00
-- url     : https://prove2.me/submissions/5b5310af-039e-4a4d-b512-4a0acf466fec

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
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
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]













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
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set




variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]









namespace MarkovProcess.Kernel.IsSupportedOnContinuousPaths

end MarkovProcess.Kernel.IsSupportedOnContinuousPaths
open MarkovProcess.Kernel.IsSupportedOnContinuousPaths
theorem solution
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default₁ default₂ : ContinuousPath alpha) :
    toContinuousPathKernel κ default₁ = toContinuousPathKernel κ default₂ := by
  rw [toContinuousPathKernel_eq_map, toContinuousPathKernel_eq_map]
  ext x s hs
  rw [Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₁) x hs,
    Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₂) x hs]
  have hfun : ContinuousPath.continuousExtension default₁ =ᵐ[κ x]
      ContinuousPath.continuousExtension default₂ :=
    (hκ x).mono fun path hpath ↦ by
      obtain ⟨omega, rfl⟩ := hpath
      rw [ContinuousPath.continuousExtension_denseRestriction,
        ContinuousPath.continuousExtension_denseRestriction]
  exact measure_congr (hfun.preimage s)
