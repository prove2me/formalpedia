-- Prove2me | solution 1 for MarkovProcess.Kernel.IsSupportedOnContinuousPaths.map_denseRestriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:04:27.284925+00:00
-- url     : https://prove2.me/submissions/08863b08-e912-4acb-a86f-c1b2f91371d0

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

open MarkovProcess MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]











@[simp]
theorem continuousExtension_denseRestriction [T2Space alpha]
    (default omega : ContinuousPath alpha) :
    continuousExtension (alpha := alpha) default (denseRestriction omega) = omega := by
  exact Function.Injective.extend_apply denseRestriction_injective _ _ _

theorem denseRestriction_continuousExtension_of_mem_range [T2Space alpha]
    (default : ContinuousPath alpha) {x : DenseTime → alpha}
    (hx : x ∈ Set.range (denseRestriction (alpha := alpha))) :
    denseRestriction (continuousExtension (alpha := alpha) default x) = x := by
  obtain ⟨omega, rfl⟩ := hx
  rw [continuousExtension_denseRestriction]
end ContinuousPath
end
end MarkovProcess
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


noncomputable section


variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]












theorem solution
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default : ContinuousPath alpha) :
    (toContinuousPathKernel κ default).map ContinuousPath.denseRestriction = κ := by
  rw [toContinuousPathKernel_eq_map, ← Kernel.map_comp_right]
  · ext x s hs
    rw [Kernel.map_apply' _
      ((ContinuousPath.measurable_denseRestriction).comp
        (ContinuousPath.measurable_continuousExtension default)) x hs]
    have hfun :
        ContinuousPath.denseRestriction ∘ ContinuousPath.continuousExtension default
          =ᵐ[κ x] id :=
      (hκ x).mono fun path hpath ↦
        ContinuousPath.denseRestriction_continuousExtension_of_mem_range default hpath
    simpa only [Set.preimage_id] using measure_congr (hfun.preimage s)
  · exact ContinuousPath.measurable_continuousExtension default
  · exact ContinuousPath.measurable_denseRestriction
