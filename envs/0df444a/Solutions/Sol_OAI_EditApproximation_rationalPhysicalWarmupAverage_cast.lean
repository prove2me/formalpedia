-- Prove2me | solution 1 for OAI.EditApproximation.rationalPhysicalWarmupAverage_cast
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:34.998255+00:00
-- url     : https://prove2.me/submissions/01b18826-1654-4216-be01-6ab4426ec8f6

import Mathlib
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmup_cast

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRationalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



theorem rationalPhysicalWarmupAverage_cast_oai {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalWarmupAverage source target P L initial representatives T state : ℝ) =
      physicalWarmupAverage source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives T state := by
  simp only [rationalPhysicalWarmupAverage, physicalWarmupAverage, warmupAverage,
    Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, rationalPhysicalWarmup_cast, physicalWarmup]

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.rationalPhysicalWarmupAverage_cast_oai.{u_1} := @OAI.EditApproximation.rationalPhysicalWarmupAverage_cast_oai.{u_1}
