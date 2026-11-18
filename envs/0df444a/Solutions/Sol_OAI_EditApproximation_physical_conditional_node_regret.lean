-- Prove2me | solution 1 for OAI.EditApproximation.physical_conditional_node_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:35.177201+00:00
-- url     : https://prove2.me/submissions/0ed34b64-0626-4ec9-838b-0817321bd59f

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalBand_prefix_expected_regret
import Theorems.Thm_OAI_EditApproximation_physicalNode_firstCrossing_regret
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_shift_square (ell : ℕ) (hell : 1764 ≤ ell) :
    ((coarseExponent ell : ℝ) + 21) ^ 2 ≤ ell := by
  have hp : (coarseExponent ell : ℝ) ^ 4 ≤ ell := by
    exact_mod_cast (coarseExponent_fourth_power ell).trans (Nat.log_le_self 2 ell)
  have hellR : (1764 : ℝ) ≤ ell := by exact_mod_cast hell
  have hscaled : (4 * (coarseExponent ell : ℝ) ^ 2) ^ 2 ≤ (ell : ℝ) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16)
    have hb : 16 * (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hquarter : 4 * (coarseExponent ell : ℝ) ^ 2 ≤ ell :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg ell)).mp hscaled
  nlinarith [sq_nonneg ((coarseExponent ell : ℝ) - 21)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandEnvelopes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual dyadic child envelopes

The maximum scans the actual finite band. The dyadic ceiling uses the
computable integer upper logarithm of a positive rational, including values
below one.
-/

namespace EditApproximation

open Finset



theorem le_rationalMaximum_member (fallback : ℚ) (values : List ℚ) (value : ℚ)
    (hvalue : value ∈ values) : value ≤ rationalMaximum fallback values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons head rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact le_max_left _ _
    · exact (ih hrest).trans (le_max_right _ _)



/-- Zero is a harmless duplicated fallback under the initial table lower
invariant. The positive b/M floor ensures that the ceiling input is positive. -/


theorem bandChildEnvelope_lower {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (b : ℚ) / M ≤ bandChildEnvelope b band initial i ∧
      ∀ action ∈ band, initial i (action i) ≤ bandChildEnvelope b band initial i := by
  have hceil := Int.self_le_zpow_clog (R := ℚ) (by decide : 1 < 2)
    (max ((b : ℚ) / M) (rationalMaximum 0 (band.map fun action => initial i (action i))))
  refine ⟨(le_max_left _ _).trans hceil, ?_⟩
  intro action ha
  exact (le_rationalMaximum_member 0 _ _ (List.mem_map.mpr ⟨action, ha, rfl⟩)).trans
    ((le_max_right _ _).trans hceil)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRounding
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer rounding spacings from the dyadic band envelopes

Taking the nonnegative part of the dyadic product exponent computes the
integer spacing max(1, theta*h). The resulting spacing preserves the wide
grid by actual divisibility of powers of two.
-/

namespace EditApproximation

open Finset





/-- Actual division rounding moves each endpoint by at most the scaled
child envelope, including the special spacing-one case. -/
theorem gridRound_scaled_error (spacing position : ℕ) (scaled : ℚ)
    (hspacing : (spacing : ℚ) = max 1 scaled) (hscaled : 0 ≤ scaled) :
    (Nat.dist position (gridRound spacing position) : ℚ) ≤ scaled := by
  have hpos : 0 < spacing := by
    have hone : (1 : ℚ) ≤ spacing := by rw [hspacing]; exact le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hone)
  by_cases hone : spacing = 1
  · simp only [hone, gridRound_one, Nat.dist_self, Nat.cast_zero]
    exact hscaled
  · have htwo : 1 < spacing := by omega
    have htwoR : (1 : ℚ) < spacing := by exact_mod_cast htwo
    have hscale : 1 < scaled := by
      by_contra hnot
      have hle : scaled ≤ 1 := le_of_not_gt hnot
      rw [max_eq_left hle] at hspacing
      linarith only [hspacing, htwoR]
    have hequal : (spacing : ℚ) = scaled := hspacing.trans (max_eq_right hscale.le)
    have herr : (Nat.dist position (gridRound spacing position) : ℚ) < spacing := by
      exact_mod_cast gridRound_error_lt spacing position hpos
    exact herr.le.trans_eq hequal

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual rounded band actions pass the finite guards

Each child uses its own envelope-derived integer spacing. The action is
rounded with literal integer division; wide-grid, radius and imbalance
claims are proved for these returned states.
-/

namespace EditApproximation

open Finset





theorem bandChildEnvelope_pos {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    0 < bandChildEnvelope b band initial i := by
  unfold bandChildEnvelope rationalDyadicCeiling
  positivity

theorem roundedBandAction_endpoint_error {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (Nat.dist (action i).lo (roundedBandAction thetaExponent b band initial action i).lo : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i ∧
      (Nat.dist (action i).hi (roundedBandAction thetaExponent b band initial action i).hi : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have hscaled : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le (bandChildEnvelope_pos b band initial i).le
  exact ⟨gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled,
    gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled⟩

theorem roundedBandAction_distance {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := roundedBandAction_endpoint_error thetaExponent b band initial action i
  unfold targetEndpointDistance
  push_cast
  convert add_le_add h.1 h.2 using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The initial table's literal spatial bound controls the value of every
returned rounded state. -/
theorem roundedBandAction_initialValue {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    initial i (roundedBandAction thetaExponent b band initial action i) ≤ initial i (action i) +
      2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := hspatial i (roundedBandAction thetaExponent b band initial action i) (action i)
  have hsym : targetEndpointDistance (roundedBandAction thetaExponent b band initial action i) (action i) =
      targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) := by
    unfold targetEndpointDistance
    rw [Nat.dist_comm (roundedBandAction thetaExponent b band initial action i).lo,
      Nat.dist_comm (roundedBandAction thetaExponent b band initial action i).hi]
  rw [hsym] at h
  have hmove := mul_le_mul_of_nonneg_left
    (roundedBandAction_distance thetaExponent b band initial action i) hL0
  nlinarith only [h, hmove]

theorem roundedBandAction_initialValue_le_twice {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny)
    (haction : action ∈ band) (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    initial i (roundedBandAction thetaExponent b band initial action i) ≤
      2 * bandChildEnvelope b band initial i := by
  have hbefore := (bandChildEnvelope_lower b band initial i).2 action haction
  have hafter := roundedBandAction_initialValue thetaExponent b band initial action L0 hL0 hspatial i
  have hmove := mul_le_mul_of_nonneg_right hsmall (bandChildEnvelope_pos b band initial i).le
  nlinarith only [hbefore, hafter, hmove]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSampling
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniform sampling

The shared group estimator samples child labels uniformly with replacement.
These lemmas use that finite distribution, including its product law;
they do not assume that different group representatives are independent.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem uniform_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, value i ∂(PMF.uniformOfFintype ι).toMeasure) = uniformMean value := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← mul_sum, uniformMean]
  ring

theorem uniformMean_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound) :
    0 ≤ uniformMean value ∧ uniformMean value ≤ bound := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (sum_nonneg fun i _ => (hvalue i).1) hc.le
  · apply (div_le_iff₀ hc).2
    have hsum := sum_le_sum (s := univ) fun i _ => (hvalue i).2
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_comm] using hsum

theorem uniform_centered_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound)
    (i : ι) : |value i - uniformMean value| ≤ bound := by
  have hm := uniformMean_bounds value hvalue
  exact abs_le.mpr ⟨by linarith [(hvalue i).1], by linarith [(hvalue i).2]⟩

theorem uniform_centered_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, (value i - uniformMean value)
      ∂(PMF.uniformOfFintype ι).toMeasure) = 0 := by
  rw [integral_sub (.of_finite) (integrable_const _), uniform_integral, integral_const]
  simp

theorem uniform_variance_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound) :
    (∫ i, (value i - uniformMean value) ^ 2
      ∂(PMF.uniformOfFintype ι).toMeasure) ≤ bound * uniformMean value := by
  let μ := (PMF.uniformOfFintype ι).toMeasure
  have hmean : (∫ i, value i ∂μ) = uniformMean value := uniform_integral value
  have hexpand : (∫ i, (value i - uniformMean value) ^ 2 ∂μ) =
      (∫ i, value i ^ 2 ∂μ) - (uniformMean value) ^ 2 := by
    calc
      _ = ∫ i, (value i ^ 2 - 2 * uniformMean value * value i +
          (uniformMean value) ^ 2) ∂μ := by congr 1; funext i; ring
      _ = _ := by
        rw [integral_add (.of_finite) (integrable_const _),
          integral_sub (.of_finite) (.of_finite), integral_const_mul, hmean, integral_const]
        simp only [probReal_univ, one_smul]
        ring
  have hsecond : (∫ i, value i ^ 2 ∂μ) ≤ bound * uniformMean value := by
    rw [← hmean, ← integral_const_mul]
    apply integral_mono (.of_finite) (.of_finite)
    intro i
    nlinarith [(hvalue i).1, (hvalue i).2]
  rw [hexpand]
  nlinarith [sq_nonneg (uniformMean value)]

/-- Actual independent uniform draws, centered and divided by the sample
count. All measurability, centering and variance obligations for Bernstein
are derived from this product distribution. -/
theorem uniform_sample_average_concentration
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n : ℕ) (hn : 0 < n) (value : ι → ℝ) (bound meanBound deviation : ℝ)
    (hbound : 0 < bound) (hmeanBound : 0 < meanBound) (hdev : 0 < deviation)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound)
    (hmean : uniformMean value ≤ meanBound)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure)) :
    (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure).real
      {ω | deviation ≤ |(∑ j : Fin n, value (ω j)) / n - uniformMean value|} ≤
      2 * Real.exp (-(n : ℝ) * deviation ^ 2 /
        (2 * bound * meanBound + (2 / 3 : ℝ) * bound * deviation)) := by
  let μ := (PMF.uniformOfFintype ι).toMeasure
  let X : Fin n → (Fin n → ι) → ℝ :=
    fun j ω => (value (ω j) - uniformMean value) / n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hindep : iIndepFun X (Measure.pi fun _ : Fin n => μ) := by
    exact iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ i => (value i - uniformMean value) / n)
      (fun _ => (measurable_of_finite _).aemeasurable)
  have hcenter : ∀ j, (∫ ω, X j ω ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
    intro j
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin n => μ) (i := j)
      (f := fun i => (value i - uniformMean value) / n)
      (measurable_of_finite _).aestronglyMeasurable]
    rw [integral_div, uniform_centered_integral, zero_div]
  have hbounded : ∀ j, ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
      |X j ω| ≤ bound / n := by
    intro j
    filter_upwards [] with ω
    dsimp [X]
    rw [abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right (uniform_centered_bound value hvalue _) hnr.le
  have hvariance : (∑ j : Fin n, ∫ ω, (X j ω) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ bound * meanBound / n := by
    have hpoint (j : Fin n) : (∫ ω, (X j ω) ^ 2
        ∂Measure.pi (fun _ : Fin n => μ)) ≤ bound * meanBound / n ^ 2 := by
      dsimp [X]
      rw [integral_comp_eval (μ := fun _ : Fin n => μ) (i := j)
        (f := fun i => ((value i - uniformMean value) / n) ^ 2)
        (measurable_of_finite _).aestronglyMeasurable]
      simp_rw [div_pow]
      rw [integral_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (uniform_variance_bound value hvalue).trans
        (mul_le_mul_of_nonneg_left hmean hbound.le)
    have hsum := sum_le_sum (s := univ) fun j _ => hpoint j
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    apply hsum.trans_eq
    field_simp
  have htail := bernstein n X (bound / n) (bound * meanBound / n) deviation
    (div_pos hbound hnr) (div_pos (mul_pos hbound hmeanBound) hnr) hdev hindep
    (fun _ => measurable_of_finite _) (fun _ => .of_finite) hcenter hbounded hvariance
  have hsum (ω : Fin n → ι) : (∑ j : Fin n, X j ω) =
      (∑ j : Fin n, value (ω j)) / n - uniformMean value := by
    dsimp [X]
    rw [← sum_div, sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hsum] at htail
  convert htail using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSampling
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared group sampling

The one-scale estimator in Section 5 is a finite uniform average. Its
concentration follows from the explicitly cited Bernstein input. Choosing
among representatives and extending their costs by cones is deterministic
on the simultaneous approximation event, even when their samples are shared.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

/-- The normalized sample bounds used by the executable group estimator
follow from the rounded action's child bounds and the band sum guard. -/
theorem normalizedChildSample_moments {M : ℕ} (hM : 0 < M)
    (b h F : ℝ) (hb : 0 < b) (hh : 0 < h)
    (childScale childValue : Fin M → ℝ)
    (hscale : ∀ i, 0 ≤ childScale i)
    (hvalue : ∀ i, 0 ≤ childValue i ∧ childValue i ≤ 2 * childScale i)
    (hsum : (∑ i, childScale i) ≤ 64 * F * b) :
    (∀ i, 0 ≤ normalizedChildSample b h childScale childValue i ∧
      normalizedChildSample b h childScale childValue i ≤ 2 * ((M : ℝ) * h / b)) ∧
    uniformMean (normalizedChildSample b h childScale childValue) ≤ 128 * F := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpoint (i : Fin M) : normalizedChildSample b h childScale childValue i ≤
      (M : ℝ) / b * (2 * childScale i) := by
    unfold normalizedChildSample
    split_ifs
    · have hmul := mul_le_mul_of_nonneg_left (hvalue i).2 (div_nonneg hMr.le hb.le)
      convert hmul using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · exact mul_nonneg (div_nonneg hMr.le hb.le)
        (mul_nonneg (by norm_num) (hscale i))
  constructor
  · intro i
    unfold normalizedChildSample
    split_ifs with hi
    · constructor
      · exact div_nonneg (mul_nonneg hMr.le (hvalue i).1) hb.le
      · have hmul := mul_le_mul_of_nonneg_left (hvalue i).2 hMr.le
        rw [hi] at hmul
        calc
          _ ≤ (2 * ((M : ℝ) * h)) / b :=
            div_le_div_of_nonneg_right (by nlinarith :
              (M : ℝ) * childValue i ≤ 2 * ((M : ℝ) * h)) hb.le
          _ = _ := by ring
    · constructor
      · rfl
      · positivity
  · unfold uniformMean
    rw [Fintype.card_fin]
    apply (div_le_iff₀ hMr).2
    have hsumPoint := sum_le_sum (s := univ) fun i _ => hpoint i
    rw [← mul_sum, ← mul_sum] at hsumPoint
    have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * M / b)
    have hid : (M : ℝ) / b * (2 * ∑ i, childScale i) =
        (2 * M / b) * ∑ i, childScale i := by ring
    rw [hid] at hsumPoint
    have hcancel : (2 * M / b) * (64 * F * b) = 128 * F * M := by field_simp <;> ring
    rw [hcancel] at hscaled
    linarith

theorem group_bernstein_exponent {ratio F Q deviation : ℝ} {n : ℕ}
    (hratio : 0 < ratio) (hF : 0 < F) (hdev : 0 < deviation)
    (hsamples : Q * ratio ≤ n) :
    Q * deviation ^ 2 / (512 * F + (4 / 3 : ℝ) * deviation) ≤
      (n : ℝ) * deviation ^ 2 /
        (2 * (2 * ratio) * (128 * F) + (2 / 3 : ℝ) * (2 * ratio) * deviation) := by
  let den := 512 * F + (4 / 3 : ℝ) * deviation
  have hden : 0 < den := by dsimp [den] <;> positivity
  have hid : 2 * (2 * ratio) * (128 * F) + (2 / 3 : ℝ) * (2 * ratio) * deviation =
      ratio * den := by dsimp [den] <;> ring
  rw [hid]
  apply (div_le_div_iff₀ hden (mul_pos hratio hden)).2
  have hmul := mul_le_mul_of_nonneg_right hsamples
    (mul_nonneg (sq_nonneg deviation) hden.le)
  nlinarith

theorem group_scale_concentration {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n : ℕ) (hn : 0 < n) (value : ι → ℝ) (ratio F Q deviation : ℝ)
    (hratio : 0 < ratio) (hF : 0 < F) (hdev : 0 < deviation)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ 2 * ratio)
    (hmean : uniformMean value ≤ 128 * F) (hsamples : Q * ratio ≤ n)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure)) :
    (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure).real
      {ω | deviation ≤ |(∑ j : Fin n, value (ω j)) / n - uniformMean value|} ≤
      2 * Real.exp (-Q * deviation ^ 2 / (512 * F + (4 / 3 : ℝ) * deviation)) := by
  have htail := uniform_sample_average_concentration n hn value
    (2 * ratio) (128 * F) deviation (by positivity) (by positivity) hdev
    hvalue hmean bernstein
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div, neg_mul] using
    neg_le_neg (group_bernstein_exponent hratio hF hdev hsamples)

/-- Shared draws may correlate all representatives. The simultaneous
event uses only finite subadditivity. -/
theorem group_failure_union_bound {Ω ι κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (members : Finset ι) (scales : Finset κ)
    (bad : ι → κ → Set Ω) (failure : ℝ)
    (hfailure : ∀ i ∈ members, ∀ h ∈ scales, μ.real (bad i h) ≤ failure) :
    μ.real (⋃ i ∈ members, ⋃ h ∈ scales, bad i h) ≤
      (members.card : ℝ) * scales.card * failure := by
  apply (measureReal_biUnion_finset_le members _).trans
  have hmember (i : ι) (hi : i ∈ members) :
      μ.real (⋃ h ∈ scales, bad i h) ≤ (scales.card : ℝ) * failure := by
    apply (measureReal_biUnion_finset_le scales _).trans
    have hsum := sum_le_sum (s := scales) fun h hh => hfailure i hi h hh
    simpa only [sum_const, nsmul_eq_mul] using hsum
  have hsum := sum_le_sum hmember
  simpa only [sum_const, nsmul_eq_mul, mul_assoc] using hsum

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_UnskippedBands
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Literal unskipped-band tests

The finite representative band, rational child envelopes and canonical
rounded action are tested directly. A successful result carries exactly
the facts checked by the algorithm; inaccurate seeds still produce a
finite list of such tested records.
-/

namespace EditApproximation

open Finset







namespace UnskippedBand







theorem envelope_pos {α : Type*} {source target : List α} {M : ℕ}
    {parent : TargetInterval source.length} {b P thetaExponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) (i : Fin M) :
    0 < member.envelope i :=
  bandChildEnvelope_pos b member.actions initial i

end UnskippedBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem integerClosedRange_mem (lo hi value : ℤ) :
    value ∈ integerClosedRange lo hi ↔ lo ≤ value ∧ value ≤ hi := by
  constructor
  · intro h
    obtain ⟨i, hi', hequal⟩ := List.mem_map.mp h
    have hrange := List.mem_range.mp hi'
    omega
  · rintro ⟨hlower, hupper⟩
    apply List.mem_map.mpr
    refine ⟨(value - lo).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem integerClosedRange_nodup (lo hi : ℤ) : (integerClosedRange lo hi).Nodup := by
  apply List.Nodup.map _ (List.nodup_range)
  intro i j hequal
  change lo + (i : ℤ) = lo + (j : ℤ) at hequal
  omega



theorem groupDyadicScales_mem {M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (F : ℚ) (hF : 0 < F) (exponent : ℤ) :
    (2 : ℚ) ^ exponent ∈ groupDyadicScales M b F ↔
      (b : ℚ) / M ≤ (2 : ℚ) ^ exponent ∧ (2 : ℚ) ^ exponent ≤ 64 * F * b := by
  have hlower : (0 : ℚ) < (b : ℚ) / M := by positivity
  have hupper : (0 : ℚ) < 64 * F * b := by positivity
  constructor
  · intro h
    obtain ⟨other, hother, hequal⟩ := List.mem_map.mp h
    have hsame : other = exponent :=
      zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1) hequal
    subst other
    have hrange := (integerClosedRange_mem _ _ _).mp hother
    exact ⟨(Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mpr hrange.1,
      (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mpr hrange.2⟩
  · rintro ⟨hlow, hhigh⟩
    apply List.mem_map.mpr
    refine ⟨exponent, (integerClosedRange_mem _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
    · exact (Int.le_zpow_iff_clog_le (by decide : 1 < 2) hlower).mp hlow
    · exact (Int.zpow_le_iff_le_log (by decide : 1 < 2) hupper).mp hhigh

theorem groupDyadicScales_nodup (M b : ℕ) (F : ℚ) : (groupDyadicScales M b F).Nodup := by
  exact (integerClosedRange_nodup _ _).map
    (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1))

theorem groupDyadicScales_pos {M b : ℕ} {F h : ℚ}
    (hh : h ∈ groupDyadicScales M b F) : 0 < h := by
  obtain ⟨exponent, _, rfl⟩ := List.mem_map.mp hh
  positivity



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

theorem groupSampleCount_pos {M Q b : ℕ} {h : ℚ}
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (hh : 0 < h) :
    0 < groupSampleCount M Q b h := by
  exact lt_min hM (Nat.ceil_pos.mpr (by positivity))

theorem groupSampleCount_sampled {M Q b : ℕ} {h : ℚ}
    (hsampled : groupSampleCount M Q b h < M) :
    (Q : ℚ) * M * h / b ≤ groupSampleCount M Q b h := by
  have hceil : groupSampleCount M Q b h = ⌈(Q : ℚ) * M * h / b⌉₊ := by
    unfold groupSampleCount at hsampled ⊢
    omega
  rw [hceil]
  exact Nat.le_ceil _





/-- The sample and actual scale cost have exactly the normalized average
used in the published Bernstein specialization. -/
theorem groupScaleEstimate_normalized {M b k : ℕ} (h : ℚ)
    (envelope value : Fin M → ℚ) (draw : Fin k → Fin M)
    (hM : 0 < M) (hb : 0 < b) (hk : 0 < k) (hsampled : k ≠ M) :
    ((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ) =
      (b : ℝ) * ((∑ j, normalizedChildSample (b : ℝ) (h : ℝ)
        (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)) (draw j)) / k -
          uniformMean (normalizedChildSample (b : ℝ) (h : ℝ)
            (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)))) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hcast (i : Fin M) : normalizedChildSample (b : ℝ) (h : ℝ)
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ)) i =
        (M : ℝ) / b * ((if envelope i = h then value i else 0 : ℚ) : ℝ) := by
    by_cases hequal : envelope i = h
    · simp only [normalizedChildSample, hequal, ↓reduceIte]
      ring
    · have hequalR : (envelope i : ℝ) ≠ (h : ℝ) := by exact_mod_cast hequal
      simp only [normalizedChildSample, hequal, hequalR, ↓reduceIte, Rat.cast_zero, mul_zero]
  unfold uniformMean
  simp_rw [hcast]
  simp only [groupScaleEstimate, hsampled, ↓reduceIte, groupScaleTrueCost,
    Fintype.card_fin, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_sum]
  rw [← mul_sum, ← mul_sum]
  field_simp

theorem groupScaleEstimate_concentration {M Q b k : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (h F deviation : ℚ)
    (hh : 0 < h) (hF : 0 < F) (hdev : 0 < deviation)
    (envelope value : Fin M → ℚ)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ 2 * envelope i)
    (hsum : (∑ i, envelope i) ≤ 64 * F * b)
    (hcount : k = groupSampleCount M Q b h)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin M)).toMeasure).real
      {draw | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} ≤
      2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
        (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation)) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hdevr : (0 : ℝ) < deviation := by exact_mod_cast hdev
  by_cases hexact : k = M
  · have hempty : {draw : Fin k → Fin M | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} = ∅ := by
      ext draw
      simp only [groupScaleEstimate, hexact, ↓reduceIte, sub_self, Rat.cast_zero, abs_zero,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (mul_pos hdevr hbr)
    rw [hempty, measureReal_empty]
    positivity
  · have hsampled : groupSampleCount M Q b h < M := by
      have hle : groupSampleCount M Q b h ≤ M := min_le_left _ _
      omega
    have hk : 0 < k := hcount ▸ groupSampleCount_pos hM hQ hb hh
    let sample := normalizedChildSample (b : ℝ) (h : ℝ)
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ))
    have hmoments := normalizedChildSample_moments hM (b : ℝ) (h : ℝ) (F : ℝ) hbr hhr
      (fun i => (envelope i : ℝ)) (fun i => (value i : ℝ))
      (fun i => by exact_mod_cast henvelope i)
      (fun i => by exact_mod_cast hvalue i) (by exact_mod_cast hsum)
    have hsamples : (Q : ℝ) * ((M : ℝ) * (h : ℝ) / b) ≤ k := by
      have hsampleLower := groupSampleCount_sampled hsampled
      rw [← hcount] at hsampleLower
      have hcast : (Q : ℝ) * M * (h : ℝ) / b ≤ k := by exact_mod_cast hsampleLower
      convert hcast using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have htail := group_scale_concentration k hk sample ((M : ℝ) * (h : ℝ) / b)
      (F : ℝ) (Q : ℝ) (deviation : ℝ) (by positivity) hFr hdevr
      hmoments.1 hmoments.2 hsamples bernstein
    have hevent : {draw : Fin k → Fin M | (deviation : ℝ) * b ≤
        |((groupScaleEstimate k h envelope value draw - groupScaleTrueCost h envelope value : ℚ) : ℝ)|} =
        {draw | (deviation : ℝ) ≤ |(∑ j, sample (draw j)) / k - uniformMean sample|} := by
      ext draw
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        groupScaleEstimate_normalized h envelope value draw hM hb hk hexact,
        abs_mul, abs_of_pos hbr, mul_comm (deviation : ℝ) (b : ℝ)]
      exact mul_le_mul_iff_right₀ hbr
    rw [hevent]
    exact htail

theorem groupSharedDraw_projection {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin T → ℕ) (scale : Fin T) (bad : Set (Fin (count scale) → Fin M)) :
    (groupSharedDrawLaw count).real {draw | draw scale ∈ bad} =
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure).real bad := by
  let ν (scale : Fin T) :=
    Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure
  have hmap := (measurePreserving_eval (μ := ν) scale).map_eq
  have hpreimage := Measure.map_apply (μ := Measure.pi ν) (measurable_pi_apply scale)
    (Set.toFinite bad).measurableSet
  rw [hmap] at hpreimage
  exact congrArg ENNReal.toReal hpreimage.symm

theorem groupScaleTrueCost_sum {M T : ℕ} (scales : Fin T → ℚ)
    (hinjective : Function.Injective scales) (envelope value : Fin M → ℚ)
    (hcover : ∀ i, ∃ scale, scales scale = envelope i) :
    (∑ scale, groupScaleTrueCost (scales scale) envelope value) = ∑ i, value i := by
  unfold groupScaleTrueCost
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  obtain ⟨scale, hscale⟩ := hcover i
  have h : (∑ other : Fin T, if scales scale = scales other then value i else 0) = value i := by
    simp only [hinjective.eq_iff, sum_ite_eq, mem_univ, ↓reduceIte]
  simpa only [hscale] using h

theorem groupMemberEstimate_error {M T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hinjective : Function.Injective scales) (connection : ℚ) (envelope value : Fin M → ℚ)
    (hcover : ∀ i, ∃ scale, scales scale = envelope i)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) (error : ℚ)
    (herror : ∀ scale, |groupScaleEstimate (count scale) (scales scale) envelope value (draw scale) -
        groupScaleTrueCost (scales scale) envelope value| ≤ error) :
    |groupMemberEstimate scales count connection envelope value draw - (connection + ∑ i, value i)| ≤
      T * error := by
  rw [← groupScaleTrueCost_sum scales hinjective envelope value hcover]
  unfold groupMemberEstimate
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hsum := sum_le_sum (s := univ) fun scale _ => herror scale
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

section ActualUnskippedGroup

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
  {parent : TargetInterval source.length} {tau F : ℚ}
  {child initial : Fin M → TargetInterval target.length → ℚ}

theorem unskippedBand_envelope_scale
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hM : 0 < M) (hb : 0 < b) (hF : 0 < F) (i : Fin M) :
    member.envelope i ∈ groupDyadicScales M b F := by
  have hlower := (bandChildEnvelope_lower b member.actions initial i).1
  change (b : ℚ) / M ≤ member.envelope i at hlower
  have hsingle : member.envelope i ≤ ∑ j, member.envelope j :=
    single_le_sum (fun j _ => (member.envelope_pos j).le) (mem_univ i)
  have hupper := hsingle.trans member.sum_guard
  have hpower : member.envelope i = (2 : ℚ) ^ bandEnvelopeExponent b member.actions initial i := rfl
  rw [hpower]
  exact (groupDyadicScales_mem hM hb F hF _).mpr ⟨by simpa only [hpower] using hlower,
    by simpa only [hpower] using hupper⟩

theorem unskippedBand_rounded_value_bounds
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (value : Fin M → TargetInterval target.length → ℚ) (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s) (i : Fin M) :
    0 ≤ value i (member.rounded i) ∧ value i (member.rounded i) ≤ 2 * member.envelope i := by
  refine ⟨(hvalue i (member.rounded i)).1, (hvalue i (member.rounded i)).2.trans ?_⟩
  exact roundedBandAction_initialValue_le_twice thetaExponent b member.actions initial
    (member.actions.head member.nonempty) (List.head_mem member.nonempty) L0 hL0 hsmall hspatial i










theorem unskippedGroupEstimate_error {T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b F)
    (value : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hM : 0 < M) (hb : 0 < b) (hF : 0 < F)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) (error : ℚ)
    (herror : ∀ scale, |groupScaleEstimate (count scale) (scales scale) member.envelope
      (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i))| ≤ error) :
    |unskippedGroupEstimate scales count value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ T * error := by
  have hinjective : Function.Injective scales := List.nodup_ofFn.mp
    (hscales.symm ▸ groupDyadicScales_nodup M b F)
  have hcover (i : Fin M) : ∃ scale, scales scale = member.envelope i := by
    have hmember := unskippedBand_envelope_scale member hM hb hF i
    rw [← hscales] at hmember
    exact List.mem_ofFn.mp hmember
  exact groupMemberEstimate_error scales count hinjective _ member.envelope
    (fun i => value i (member.rounded i)) hcover draw error herror

/-- Uniform simultaneous accuracy for the actual fixed list of unskipped
records. The same per-scale samples are reused by every record. -/
theorem unskippedGroupEstimate_failure {T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (scales : Fin T → ℚ) (count : Fin T → ℕ) (Q : ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b F)
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hM : 0 < M) (hQ : 0 < Q) (hb : 0 < b) (hF : 0 < F)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s)
    (deviation : ℚ) (hdev : 0 < deviation)
    (bernstein : ∀ scale : Fin T, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      (members.length : ℝ) * T *
        (2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
          (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation))) := by
  classical
  let μ := groupSharedDrawLaw (M := M) count
  let : IsProbabilityMeasure μ := by dsimp only [μ]; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  let bad (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (scale : Fin T) : Set (∀ scale : Fin T, Fin (count scale) → Fin M) :=
    {draw | (deviation : ℝ) * b ≤
      |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope
          (fun i => value i (member.rounded i)) : ℚ) : ℝ)|}
  let failure := 2 * Real.exp (-(Q : ℝ) * (deviation : ℝ) ^ 2 /
    (512 * (F : ℝ) + (4 / 3 : ℝ) * deviation))
  have hpoint (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (_hmember : member ∈ members.toFinset) (scale : Fin T) (_hscale : scale ∈ (univ : Finset (Fin T))) :
      μ.real (bad member scale) ≤ failure := by
    have hscaleMember : scales scale ∈ groupDyadicScales M b F := by
      rw [← hscales]
      exact List.mem_ofFn.mpr ⟨scale, rfl⟩
    have hscalePos := groupDyadicScales_pos hscaleMember
    change μ.real {draw | draw scale ∈ {sample |
      (deviation : ℝ) * b ≤
      |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) sample -
        groupScaleTrueCost (scales scale) member.envelope
          (fun i => value i (member.rounded i)) : ℚ) : ℝ)|}} ≤ failure
    rw [groupSharedDraw_projection]
    exact groupScaleEstimate_concentration hM hQ hb (scales scale) F deviation hscalePos hF hdev
      member.envelope (fun i => value i (member.rounded i)) (fun i => (member.envelope_pos i).le)
      (unskippedBand_rounded_value_bounds member value L0 hL0 hsmall hspatial hvalue)
      member.sum_guard (hcount scale) (bernstein scale)
  have hsubset : {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ⊆
      ⋃ member ∈ members.toFinset, ⋃ scale ∈ (univ : Finset (Fin T)), bad member scale := by
    intro draw hdraw
    obtain ⟨member, hmember, herror⟩ := hdraw
    by_contra hnot
    have hscaleError (scale : Fin T) :
        |groupScaleEstimate (count scale) (scales scale) member.envelope
            (fun i => value i (member.rounded i)) (draw scale) -
          groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i))| ≤ deviation * b := by
      have hnotScale : draw ∉ bad member scale := by
        intro hbad
        apply hnot
        exact Set.mem_iUnion.mpr ⟨member, Set.mem_iUnion.mpr ⟨List.mem_toFinset.mpr hmember,
          Set.mem_iUnion.mpr ⟨scale, Set.mem_iUnion.mpr ⟨mem_univ scale, hbad⟩⟩⟩⟩
      have hlt : |((groupScaleEstimate (count scale) (scales scale) member.envelope
          (fun i => value i (member.rounded i)) (draw scale) -
        groupScaleTrueCost (scales scale) member.envelope (fun i => value i (member.rounded i)) : ℚ) : ℝ)| <
          (deviation : ℝ) * b := lt_of_not_ge hnotScale
      exact_mod_cast hlt.le
    have htotal := unskippedGroupEstimate_error scales count hscales value member hM hb hF draw
      (deviation * b) hscaleError
    have htotalR : |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)| ≤
        (T : ℝ) * (deviation : ℝ) * b := by
      have hcast : |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)| ≤
          (T : ℝ) * ((deviation : ℝ) * b) := by exact_mod_cast htotal
      simpa only [mul_assoc] using hcast
    exact (not_lt_of_ge htotalR) herror
  have hunion := group_failure_union_bound μ members.toFinset (univ : Finset (Fin T)) bad failure hpoint
  have hcard : (members.toFinset.card : ℝ) ≤ members.length := by exact_mod_cast members.toFinset_card_le
  have hfailure : 0 ≤ (T : ℝ) * failure := by dsimp [failure] <;> positivity
  calc
    _ ≤ μ.real (⋃ member ∈ members.toFinset, ⋃ scale ∈ (univ : Finset (Fin T)), bad member scale) :=
      measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ (members.toFinset.card : ℝ) * T * failure := by simpa only [card_univ, Fintype.card_fin] using hunion
    _ ≤ (members.length : ℝ) * T * failure := by
      first | (convert mul_le_mul_of_nonneg_right hcard hfailure using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_right hcard hfailure).trans (le_of_eq (by ring)))



end ActualUnskippedGroup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellGridPoints_length_le {side : ℚ} {g cell P : ℕ}
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellGridPoints side g cell).length ≤ P := by
  have hbase : 0 ≤ (cell : ℚ) * side / g :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hside) (Nat.cast_nonneg _)
  have hupper : ((cell : ℚ) + 1) * side / g ≤ (cell : ℚ) * side / g + P := by
    calc
      _ = (cell : ℚ) * side / g + side / g := by ring
      _ ≤ _ := add_le_add_right hsize _
  have hceil := Nat.ceil_le_ceil hupper
  rw [Nat.ceil_add_natCast hbase P] at hceil
  simp only [cellGridPoints, List.length_map, List.length_range']
  omega



theorem cellTargetStates_length_le {n g P : ℕ} {side : ℚ} (cell : ℕ × ℕ)
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellTargetStates n g side cell).length ≤ P ^ 2 := by
  have hfirst := cellGridPoints_length_le (cell := cell.1) hside hsize
  have hsecond := cellGridPoints_length_le (cell := cell.2) hside hsize
  have h := list_flatMap_length_le (cellGridPoints side g cell.1)
    (fun lo => (cellGridPoints side g cell.2).filterMap fun hi => makeTargetState n lo hi) P
    (fun lo _ => (List.length_filterMap_le _ _).trans hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right P hfirst)

theorem seedGridSpacing_covers_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    b ≤ P * seedGridSpacing b P := by
  obtain ⟨eb, rfl⟩ := hb
  obtain ⟨eP, rfl⟩ := hP
  by_cases horder : eP ≤ eb
  · rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow,
      ← pow_add, Nat.add_sub_of_le horder]
  · have hle : 2 ^ eb ≤ 2 ^ eP := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact hle.trans (Nat.le_mul_of_pos_right _ (by unfold seedGridSpacing; omega))

theorem cellRepresentativeStates_length_le {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellRepresentativeStates n P F b a initial theta cell).length ≤ (P + 1) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgr : (0 : ℚ) < seedGridSpacing b P := by exact_mod_cast hg
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hgr).2
    have h := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
    simp only [one_mul] at h
    exact h.trans hcover
  unfold cellRepresentativeStates
  apply (List.length_filter_le _ _).trans
  exact (cellTargetStates_length_le (n := n) cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hsize).trans
      (Nat.pow_le_pow_left (Nat.le_succ P) 2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CellGroupSelection
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal unskipped groups of whole cells and their selected wide actions. -/

namespace EditApproximation

open Finset



theorem cellUnskippedBands_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F thetaExponent : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell).length ≤
      (P + 1) ^ 2 := by
  have htheta : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) ∧
      (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 := by
    refine ⟨(zpow_pos (by norm_num : (0 : ℚ) < 2) _).le, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
  exact (List.length_filterMap_le _ _).trans
    (cellRepresentativeStates_length_le a parentInitial _ cell htheta hb hP)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_FirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual first crossing of a finite action band

The crossing index is computed from the fixed child tables for analysis.
It is independent of parent sampling. The lemmas separate the prefixPayoff,
the single crossing, and the nonpositive later clipped regrets.
-/

namespace EditApproximation

open Finset

theorem firstCrossing_le {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) :
    firstCrossing band S actionCost c ≤ S := by
  unfold firstCrossing
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupNumerical
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit numerical slack for the shared group estimator and online increments. -/

namespace EditApproximation

theorem group_normalized_exponent {ell : ℝ} (hell : 1 ≤ ell) :
    ell ^ 37 / 3000 ≤
      ell ^ 80 * (1 / (2 * ell ^ 21)) ^ 2 /
        (512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21))) := by
  have he : 0 < ell := by linarith only [hell]
  have halpha : 0 < 1 / (2 * ell ^ 21) := by positivity
  have halpha_le : 1 / (2 * ell ^ 21) ≤ ell := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ell ^ 21)).2
    have hpow := one_le_pow₀ hell (n := 21)
    nlinarith only [hell, hpow]
  have hden : 512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21)) ≤ 750 * ell := by
    linarith only [halpha_le, hell]
  have hnum : ell ^ 80 * (1 / (2 * ell ^ 21)) ^ 2 = ell ^ 38 / 4 := by
    field_simp
    ring
  rw [hnum]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3000)
    (by positivity : 0 < 512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21)))).2
  have h := mul_le_mul_of_nonneg_left hden (pow_nonneg he.le 37)
  have hid : ell ^ 37 * (750 * ell) = ell ^ 38 / 4 * 3000 := by ring
  exact h.trans_eq hid

theorem group_exponent_polynomial_slack {ell : ℝ} (hell : 8 ≤ ell) :
    2 * ell ^ 2 + 20 * ell ≤ ell ^ 37 / 3000 := by
  have he : 1 ≤ ell := by linarith only [hell]
  have hcoef : (131072 : ℝ) ≤ ell ^ 33 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hell 6
    norm_num at h
    exact (by norm_num : (131072 : ℝ) ≤ 262144) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 6 ≤ 33)))
  have hbig : 131072 * ell ^ 4 ≤ ell ^ 37 := by
    calc
      _ ≤ ell ^ 33 * ell ^ 4 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by linarith only [hell]) 4)
      _ = _ := by ring
  have he2 : ell ≤ ell ^ 2 := by nlinarith only [he]
  have he4 : ell ^ 2 ≤ ell ^ 4 := pow_le_pow_right₀ he (by decide : 2 ≤ 4)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3000)).2
  nlinarith only [hbig, he2, he4]

/-- The union bound is below H^-4 once its literal count bounds and the
computed height/representative growth bounds have been substituted. -/
theorem group_union_failure_numeric {ell H members scales : ℝ}
    (hell : 8 ≤ ell) (hH : 0 < H) (hHexp : H ≤ Real.exp ell)
    (_hmembers : 0 ≤ members) (hmembersBound : members ≤ 4 * Real.exp (2 * ell ^ 2))
    (hscales : 0 ≤ scales) (hscalesBound : scales ≤ 2 * ell) :
    members * scales * (2 * Real.exp (-(ell ^ 37 / 3000))) ≤ 1 / H ^ 4 := by
  have he : 0 ≤ ell := by linarith only [hell]
  have hcounts : members * scales * (2 * Real.exp (-(ell ^ 37 / 3000))) ≤
      16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) := by
    have h := mul_le_mul hmembersBound hscalesBound hscales (by positivity : 0 ≤ 4 * Real.exp (2 * ell ^ 2))
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.exp (-(ell ^ 37 / 3000)))
    rw [sub_eq_add_neg, Real.exp_add]
    convert h' using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hpower : H ^ 4 ≤ Real.exp (4 * ell) := by
    have h := pow_le_pow_left₀ hH.le hHexp 4
    rw [← Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  apply (le_div_iff₀ (pow_pos hH 4)).2
  have hnonneg : 0 ≤ 16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) := by positivity
  have hprod := mul_le_mul hcounts hpower (pow_nonneg hH.le 4) hnonneg
  have hexponent := group_exponent_polynomial_slack hell
  have hsmall : 2 * ell ^ 2 - ell ^ 37 / 3000 + 4 * ell ≤ -(16 * ell) := by
    linarith only [hexponent]
  have hexp := Real.exp_le_exp.mpr hsmall
  have hlinear : 16 * ell ≤ Real.exp (16 * ell) := (Real.add_one_le_exp _).trans' (by linarith)
  have hfinal : 16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) * Real.exp (4 * ell) ≤ 1 := by
    rw [mul_assoc, ← Real.exp_add]
    calc
      _ ≤ Real.exp (16 * ell) * Real.exp (-(16 * ell)) :=
        mul_le_mul hlinear hexp (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
  exact hprod.trans hfinal

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBandSpacing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The input-computed dyadic parameters discharge all spacing and basic rounding premises. -/

namespace EditApproximation

theorem computed_theta_dyadic (N : ℕ) :
    (rationalParameters (inputSmallLog N)).theta =
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) := by
  change 1 / (((2 ^ smallLogExponent N : ℕ) : ℚ) ^ 40) = _
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  rw [Nat.mul_comm (smallLogExponent N) 40, one_div]

theorem computed_P_dyadic (N : ℕ) :
    (integerParameters N).P =
      2 ^ (heightExponent N * (coarseExponent (inputSmallLog N) + 20)) := by
  change (2 ^ heightExponent N) ^ (coarseExponent (inputSmallLog N) + 20) = _
  rw [pow_mul]

theorem basic_band_small_constants {ell : ℚ} (hell : 2 ≤ ell) :
    0 < 1 / ell ^ 4 ∧ 0 < 1 / ell ^ 40 ∧ 1 / ell ^ 40 ≤ 1 / 2 ∧
      32 * ell * (1 / ell ^ 40) ≤ 1 ∧ 64 * ell * (1 / ell ^ 40) ≤ 1 := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hcoef : (64 : ℚ) ≤ ell ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hell 6
    norm_num at h
    exact h
  have hpower : (64 : ℚ) ≤ ell ^ 39 :=
    hcoef.trans (pow_le_pow_right₀ hellone (by decide : 6 ≤ 39))
  have hscale : 64 * ell ≤ ell ^ 40 := by
    calc
      64 * ell ≤ ell ^ 39 * ell := mul_le_mul_of_nonneg_right hpower hellpos.le
      _ = ell ^ 40 := (pow_succ ell 39).symm
  have h64 : 64 * ell * (1 / ell ^ 40) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one₀ (pow_pos hellpos 40)).2 hscale
  have h32 : 32 * ell * (1 / ell ^ 40) ≤ 1 := by
    have hnonneg : 0 ≤ ell * (1 / ell ^ 40) := by positivity
    nlinarith only [h64, hnonneg]
  have htheta : 1 / ell ^ 40 ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (pow_pos hellpos 40) (by norm_num : (0 : ℚ) < 2)).2
    have h := pow_le_pow_right₀ hellone (by decide : 1 ≤ 40)
    simp only [pow_one] at h
    linarith only [hell, h]
  exact ⟨by positivity, by positivity, htheta, h32, h64⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

theorem computed_group_scale_count (N eb : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    (groupDyadicScales (integerParameters N).M (2 ^ eb) (inputSmallLog N)).length ≤
      2 * inputSmallLog N := by
  have hlogs := (inputSmallLog_bounds N hN).1
  have hsmall : smallLogExponent N ≤ inputSmallLog N :=
    (smallLogExponent N).lt_two_pow_self.le
  have hdiv := Nat.div_le_div_right (c := 20) hlogs
  change (groupDyadicScales (2 ^ (heightExponent N / 20)) (2 ^ eb)
    ((2 ^ smallLogExponent N : ℕ) : ℚ)).length ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat, groupDyadicScales_length_dyadic]
  omega

theorem computed_height_exp_upper (N : ℕ) (hN : 0 < N) :
    (inputHeight N : ℝ) ≤ Real.exp (inputSmallLog N) := by
  change ((2 ^ heightExponent N : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (heightExponent N)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  have hlogs : (heightExponent N : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast (inputSmallLog_bounds N hN).1
  exact hpower.trans (Real.exp_le_exp.mpr hlogs)

theorem computed_group_member_exp_bound (N : ℕ) (hN : 0 < N)
    (hell : 1764 ≤ inputSmallLog N) :
    (((integerParameters N).P + 1 : ℕ) : ℝ) ^ 2 ≤
      4 * Real.exp (2 * (inputSmallLog N : ℝ) ^ 2) := by
  let ell := inputSmallLog N
  let p := coarseExponent ell
  have hp := coarseExponent_shift_square ell hell
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpell : (p : ℝ) + 20 ≤ ell := by
    change ((p : ℝ) + 21) ^ 2 ≤ ell at hp
    nlinarith only [hp, hp0]
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hP : ((integerParameters N).P : ℝ) ≤ Real.exp ((ell : ℝ) ^ 2) := by
    change ((inputHeight N ^ (p + 20) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_pow]
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (inputHeight N))
      (computed_height_exp_upper N hN) (p + 20)
    rw [← Real.exp_nat_mul] at h
    have hexponent : ((p + 20 : ℕ) : ℝ) * ell ≤ (ell : ℝ) ^ 2 := by
      push_cast
      nlinarith only [hpell, hell0]
    exact h.trans (Real.exp_le_exp.mpr hexponent)
  have hPone : (1 : ℝ) ≤ (integerParameters N).P := by
    have hNat : 1 ≤ (integerParameters N).P :=
      one_le_pow₀ (Nat.one_le_two_pow (n := heightExponent N))
    exact_mod_cast hNat
  have hplus : (((integerParameters N).P + 1 : ℕ) : ℝ) ≤ 2 * Real.exp ((ell : ℝ) ^ 2) := by
    push_cast
    linarith only [hP, hPone]
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg ((integerParameters N).P + 1)) hplus 2
  rw [mul_pow, ← Real.exp_nat_mul] at hsquare
  norm_num only [Nat.cast_ofNat] at hsquare
  exact hsquare

theorem computed_group_union_failure (N eb members : ℕ) (hN : 0 < N)
    (hell : 1764 ≤ inputSmallLog N)
    (hmembers : members ≤ ((integerParameters N).P + 1) ^ 2) :
    let ell := inputSmallLog N
    let T := (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length
    (members : ℝ) * T *
      (2 * Real.exp (-((ell : ℝ) ^ 80 * (1 / (2 * (ell : ℝ) ^ 21)) ^ 2 /
        (512 * ell + (4 / 3 : ℝ) * (1 / (2 * (ell : ℝ) ^ 21)))))) ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  dsimp only
  let ell := inputSmallLog N
  let T := (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length
  have hellR : (8 : ℝ) ≤ ell := by exact_mod_cast (show 8 ≤ ell from by omega)
  have hcount : (members : ℝ) ≤ 4 * Real.exp (2 * (ell : ℝ) ^ 2) := by
    have hcast : (members : ℝ) ≤ (((integerParameters N).P + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hmembers
    exact hcast.trans (computed_group_member_exp_bound N hN hell)
  have hscale : (T : ℝ) ≤ 2 * ell := by
    exact_mod_cast computed_group_scale_count N eb hN (by omega)
  have hnum := group_union_failure_numeric hellR
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N) : (0 : ℝ) < inputHeight N)
    (computed_height_exp_upper N hN) (Nat.cast_nonneg members) hcount (Nat.cast_nonneg T) hscale
  have hexponent := group_normalized_exponent (show (1 : ℝ) ≤ ell from by linarith only [hellR])
  have hexp : Real.exp (-((ell : ℝ) ^ 80 * (1 / (2 * (ell : ℝ) ^ 21)) ^ 2 /
      (512 * ell + (4 / 3 : ℝ) * (1 / (2 * (ell : ℝ) ^ 21))))) ≤
      Real.exp (-((ell : ℝ) ^ 37 / 3000)) :=
    Real.exp_le_exp.mpr (neg_le_neg hexponent)
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2))
    (mul_nonneg (Nat.cast_nonneg members) (Nat.cast_nonneg T))).trans hnum

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupAccuracy
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual whole cell has simultaneous gamma*b accuracy with failure at most H^-4. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem computed_cellGroupEstimate_failure {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M P b Q thetaExponent T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (eb : ℕ) (hbeq : b = 2 ^ eb)
    (hQeq : Q = inputSmallLog N ^ 80) (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (parent : TargetInterval source.length) (a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b (inputSmallLog N))
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (hspatial : ∀ i s t, initial i s ≤ initial i t +
      (32 * inputSmallLog N : ℚ) * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s)
    (bernstein : ∀ scale : Fin T, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    let members := cellUnskippedBands source target parent b P (inputSmallLog N) thetaExponent
      (rationalParameters (inputSmallLog N)).tau a parentInitial child initial cell
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, ((rationalParameters (inputSmallLog N)).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  let ell := inputSmallLog N
  let members := cellUnskippedBands source target parent b P ell thetaExponent
    (rationalParameters ell).tau a parentInitial child initial cell
  let deviation : ℚ := 1 / (2 * (ell : ℚ) ^ 21)
  let μ := groupSharedDrawLaw (M := M) count
  let : IsProbabilityMeasure μ := by dsimp only [μ]; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hellQ : (2 : ℚ) ≤ ell := by exact_mod_cast (show 2 ≤ ell from by omega)
  have hellpos : (0 : ℚ) < ell := by linarith only [hellQ]
  have hb : 0 < b := hbeq ▸ Nat.two_pow_pos eb
  have hQ : 0 < Q := by rw [hQeq]; exact pow_pos (by omega : 0 < inputSmallLog N) 80
  have htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) = 1 / (ell : ℚ) ^ 40 := by
    rw [hthetaeq]
    exact (computed_theta_dyadic N).symm
  have hsmall : 2 * (32 * ell : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 := by
    rw [htheta]
    have h := (basic_band_small_constants hellQ).2.2.2.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdev : 0 < deviation := by dsimp only [deviation] <;> positivity
  have htail := unskippedGroupEstimate_failure scales count Q hscales hcount value members hM hQ hb
    hellpos (32 * ell) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsmall hspatial hvalue deviation hdev bernstein
  have hT : T ≤ 2 * ell := by
    have hlength := congrArg List.length hscales
    simp only [List.length_ofFn] at hlength
    rw [hlength, hMeq, hbeq]
    exact computed_group_scale_count N eb hN (by omega)
  have hTQ : (T : ℚ) ≤ 2 * ell := by exact_mod_cast hT
  have hbudget : (T : ℚ) * deviation ≤ (rationalParameters ell).gamma := by
    have h := mul_le_mul_of_nonneg_right hTQ hdev.le
    have hid : (2 * ell : ℚ) * deviation = (rationalParameters ell).gamma := by
      dsimp only [deviation, rationalParameters]
      field_simp
    exact h.trans_eq hid
  have hbudgetR : (T : ℝ) * (deviation : ℝ) * b ≤
      ((rationalParameters ell).gamma : ℝ) * b := by
    have h := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) b)
    exact_mod_cast h
  have hsubset : {draw | ∃ member ∈ members, ((rationalParameters ell).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ⊆
      {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} := by
    rintro draw ⟨member, hm, he⟩
    exact ⟨member, hm, hbudgetR.trans_lt he⟩
  have hmembers : members.length ≤ ((integerParameters N).P + 1) ^ 2 := by
    rw [← hPeq]
    exact cellUnskippedBands_length_le source target parent b P ell thetaExponent _ a parentInitial
      child initial cell ⟨eb, hbeq⟩ ⟨_, hPeq.trans (computed_P_dyadic N)⟩
  have hnumerical := computed_group_union_failure N eb members.length hN hell hmembers
  dsimp only at hnumerical
  have hTeq : T = (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length := by
    have hlength := congrArg List.length hscales
    simpa only [List.length_ofFn, hMeq, hbeq] using hlength
  change μ.real _ ≤ _
  apply (measureReal_mono hsubset (measure_ne_top μ _)).trans
  apply htail.trans
  rw [hQeq, hTeq]
  simpa only [deviation, ell, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_one, Nat.cast_pow, neg_mul, neg_div] using hnumerical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





theorem physicalRefinement_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rw [physicalRefinement]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  split_ifs <;>
    simp only [stageInitial, physicalInitialTable, ite_eq_left hlength,
      shortSourceCost_eq_edit _ _ hlength] <;> rfl

theorem physicalRefinement_at_last_level {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hlast : node.1.val = J) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rw [dite_eq_right (by omega : ¬ node.1.val < J)]

theorem physicalRefinement_succ {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    let children : PhysicalChildTables M target.length := fun i =>
      physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
    physicalRefinement source target U N P F A T delta choices node (t + 1) q =
      rationalWideStep (physicalSourceInterval source.length node)
        (stageRepresentatives source target U N P F A node) P
        (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
        (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
        (choices.groups node children (t + 1)) (choices.online node children (t + 1) q) q := by
  rw [physicalRefinement]
  rw [dite_eq_left hbelow, ite_eq_right hleaf]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementInvariants
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic Bellman invariants of the complete physical recurrence. -/

namespace EditApproximation

theorem stageWarmup_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    stageWarmup source target U N P F A t (node, q) =
      stageInitial source target U N P F A (node, q) := by
  cases t with
  | zero => rfl
  | succ t =>
    change rationalPhysicalBellman source target P (128 * F) _ _ _ (node, q) = _
    unfold rationalPhysicalBellman
    dsimp only
    rcases hterminal with hlast | hleaf
    · rw [dite_eq_right hlast]
    · split_ifs <;> rfl

theorem physicalRefinement_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rcases hterminal with hlast | hleaf
  · rw [dite_eq_right hlast]
  · split_ifs <;> rfl

theorem physicalRefinement_zero {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node 0 q =
      stageWarmup source target U N P F A T (node, q) := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf),
        stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
    · rw [physicalRefinement, dite_eq_left hbelow, ite_eq_right hleaf]
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow),
      stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inl hbelow)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity, exact zero states and spatial regularity of the full stage. -/

namespace EditApproximation

theorem physicalRefinement_nonneg {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  have h := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q).1
  have hzero : 0 ≤ physicalLower source target (refinementFactor A F : ℝ) (node, q) :=
    (abs_nonneg _).trans (le_max_right _ _)
  exact (Rat.cast_nonneg (K := ℝ)).mp (hzero.trans h)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalGroupAccuracy
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group concentration specialized to the actual stage and complete child histories. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem physical_cellGroupEstimate_failure {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P b Q thetaExponent K : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (eb : ℕ) (hbeq : b = 2 ^ eb)
    (hQeq : Q = inputSmallLog N ^ 80) (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P (inputSmallLog N) A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ) (cell : ℕ × ℕ)
    (scales : Fin K → ℚ) (count : Fin K → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b (inputSmallLog N))
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (bernstein : ∀ scale : Fin K, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    let F := inputSmallLog N
    let initial := fun i s => stageInitial source target U N P F A (physicalChild node hbelow i, s)
    let child := fun i s => stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s)
    let value := fun i s => physicalRefinement source target U N P F A T delta choices
      (physicalChild node hbelow i) t s
    let members := cellUnskippedBands source target (physicalSourceInterval source.length node)
      b P F thetaExponent (rationalParameters F).tau (refinementFactor A F)
      (fun s => stageInitial source target U N P F A (node, s)) child initial cell
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, ((rationalParameters F).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  have hF : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  apply computed_cellGroupEstimate_failure source target N hN hell hM hMeq hPeq eb hbeq hQeq hthetaeq
    (physicalSourceInterval source.length node) (refinementFactor A (inputSmallLog N))
    (fun s => stageInitial source target U N P (inputSmallLog N) A (node, s))
    (fun i s => stageWarmupMass source target U N P (inputSmallLog N) A T (physicalChild node hbelow i, s))
    (fun i s => stageInitial source target U N P (inputSmallLog N) A (physicalChild node hbelow i, s))
    (fun i s => physicalRefinement source target U N P (inputSmallLog N) A T delta choices
      (physicalChild node hbelow i) t s) cell scales count hscales hcount
  · intro i s r
    have hf := refinementFactor_spec A (inputSmallLog N) (by omega)
    exact physicalInitialTable_spatial source target U N P (inputSmallLog N) A
      (refinementFactor A (inputSmallLog N)) hsize hP hF hA hf.1 hf.2 hseed
      (physicalChild node hbelow i) s r
  · intro i s
    have h := physicalRefinement_stage_bounds source target hM U N P (inputSmallLog N) A
      hsize hP hF hA hseed T hT delta choices (physicalChild node hbelow i) t s
    exact ⟨physicalRefinement_nonneg source target hM U N P (inputSmallLog N) A
      hsize hP hF hA hseed T hT delta choices (physicalChild node hbelow i) t s,
      h.2.1.trans (h.2.2.1.trans h.2.2.2.1)⟩
  · exact bernstein

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

variable (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

theorem physicalBandOnlineDraw_mem (hband : band ≠ []) (η κ : ℚ) (G K t : ℕ)
    (integer : Fin (optimizerTriangularMass K)) :
    physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hband η κ G K t integer ∈ band :=
  finiteOptimizerActionDraw_mem band hband mass _ G K integer


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalExpectedRegret
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional prefix regret from the exact physical-band sampler. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory


theorem unskippedGroupFailure_true {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) (gamma : ℚ) :
    unskippedGroupFailure source target parent b P thetaExponent tau F child initial value Q members draw gamma = true ↔
      ∃ member ∈ members, gamma * b < |dyadicUnskippedGroupEstimate Q value member draw -
        rationalEndpointActionValue member.center member.rounded value| := by
  simp only [unskippedGroupFailure, List.any_eq_true, decide_eq_true_eq]

/-- Per-scale finite Bernstein bounds imply the whole-cell failure probability. -/
theorem physicalNode_groupFailure_probability {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P F b Q thetaExponent : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
    (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
    (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ) (cell : ℕ × ℕ)
    (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (groupSharedDrawLaw (fun scale : Fin (groupDyadicScales M b F).length =>
      groupSampleCount M Q b (groupDyadicScaleAt M b F scale))).real
      {draw | physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
        b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma = true} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  subst F
  let F := inputSmallLog N
  let scales := groupDyadicScaleAt M b (F : ℚ)
  let count := fun scale : Fin (groupDyadicScales M b F).length => groupSampleCount M Q b (scales scale)
  have hscales : List.ofFn scales = groupDyadicScales M b F := List.ofFn_get _
  have hprob := physical_cellGroupEstimate_failure source target N hN hell hM hMeq hPeq eb hbeq hQeq hthetaeq
    U A hsize hP hA hseed T hT delta choices node hbelow (t + 1) cell scales count hscales (fun _ => rfl) bernstein
  dsimp only at hprob
  let members := physicalNodeCellBands source target U N P F A T node hbelow
    b thetaExponent (rationalParameters F).tau cell
  let value := fun i s => physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1) (i, s)
  have hevent : {draw | physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma = true} =
      {draw | ∃ member ∈ members, ((rationalParameters F).gamma : ℝ) * b <
        |((dyadicUnskippedGroupEstimate Q value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} := by
    ext draw
    simp only [Set.mem_ofPred_eq, physicalNodeGroupFailure, unskippedGroupFailure_true]
    change (∃ member ∈ members, (rationalParameters F).gamma * b <
        |dyadicUnskippedGroupEstimate Q value member draw -
          rationalEndpointActionValue member.center member.rounded value|) ↔ _
    constructor
    · rintro ⟨member, hm, he⟩
      refine ⟨member, hm, ?_⟩
      exact_mod_cast he
    · rintro ⟨member, hm, he⟩
      refine ⟨member, hm, ?_⟩
      exact_mod_cast he
  rw [hevent]
  exact hprob

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalParentDraw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parent random streams in a fixed child environment

Finite parent arrays contain independent uniform optimizer integers and
actual shared-group draws. The projection laws are exact. Their use in the
node bound needs only the individual marginals, so no independence between
an online payoff and a group-failure indicator is asserted there.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem parentDrawLaw_online_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (payoff : Fin O → ℝ) :
    (∫ ω, payoff (parentOnlineDraw ω t) ∂parentDrawLaw R O M K count) = uniformMean payoff := by
  unfold parentOnlineDraw parentDrawLaw
  rw [integral_fun_fst (fun array : Fin R → Fin O => payoff (array (Fin.ofNat R t))), probReal_univ, one_smul, integral_comp_eval
    (μ := fun _ : Fin R => (PMF.uniformOfFintype (Fin O)).toMeasure)
    (i := Fin.ofNat R t) (f := payoff) (measurable_of_finite _).aestronglyMeasurable]
  exact uniform_integral payoff

theorem parentDrawLaw_group_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (payoff : ParentGroupDraw M K count → ℝ) :
    (∫ ω, payoff (parentGroupDraw ω t) ∂parentDrawLaw R O M K count) =
      ∫ draw, payoff draw ∂groupSharedDrawLaw (M := M) count := by
  unfold parentGroupDraw parentDrawLaw
  rw [integral_fun_snd (fun array : Fin R → ParentGroupDraw M K count => payoff (array (Fin.ofNat R t))), probReal_univ, one_smul, integral_comp_eval
    (μ := fun _ : Fin R => groupSharedDrawLaw (M := M) count)
    (i := Fin.ofNat R t) (f := payoff) (measurable_of_finite _).aestronglyMeasurable]

/-- A finite Boolean event has precisely its probability as expected indicator. -/
theorem bool_indicator_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) (failure : Ω → Bool) :
    (∫ ω, (if failure ω then (1 : ℝ) else 0) ∂μ) = μ.real {ω | failure ω = true} := by
  have hmeas : MeasurableSet {ω | failure ω = true} := Set.toFinite _ |>.measurableSet
  simpa only [Set.indicator, Pi.one_apply, Set.mem_ofPred_eq] using
    (integral_indicator_one (μ := μ) hmeas)


theorem parentDrawLaw_group_failure_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (failure : ParentGroupDraw M K count → Bool) :
    (∫ ω, (if failure (parentGroupDraw ω t) then (1 : ℝ) else 0)
      ∂parentDrawLaw R O M K count) =
      (groupSharedDrawLaw (M := M) count).real {draw | failure draw = true} := by
  rw [parentDrawLaw_group_mean R O M K count t (fun draw => if failure draw then (1 : ℝ) else 0),
    bool_indicator_integral]

/-- Integrating the deterministic first-crossing transfer needs only the
exact online marginals and per-time group probabilities. -/
theorem parentDrawLaw_firstCrossing_bound (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (S C : ℕ)
    (regret : ParentRandomSpace R O M K count → ℕ → ℝ)
    (prefixPayoff : ℕ → Fin O → ℝ) (failure : ℕ → ParentGroupDraw M K count → Bool)
    (budget crossingCharge failureCharge q : ℝ) (hcharge : 0 ≤ failureCharge)
    (hpoint : ∀ ω, (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range C, prefixPayoff t (parentOnlineDraw ω t)) + crossingCharge +
        failureCharge * ∑ t ∈ range S, (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0))
    (hprefix : (∑ t ∈ range C, uniformMean (prefixPayoff t)) ≤ budget)
    (hfailure : ∀ t < S, (groupSharedDrawLaw (M := M) count).real {draw | failure t draw = true} ≤ q) :
    (∫ ω, (∑ t ∈ range S, regret ω t) ∂parentDrawLaw R O M K count) ≤
      budget + crossingCharge + failureCharge * S * q := by
  let μ := parentDrawLaw R O M K count
  have hmean := integral_mono (μ := μ) (.of_finite) (.of_finite) hpoint
  have hprefixMean : (∫ ω, (∑ t ∈ range C, prefixPayoff t (parentOnlineDraw ω t)) ∂μ) =
      ∑ t ∈ range C, uniformMean (prefixPayoff t) := by
    rw [integral_finsetSum _ (by intro t ht; exact .of_finite)]
    exact sum_congr rfl fun t _ => parentDrawLaw_online_mean R O M K count t (prefixPayoff t)
  have hfailureMean : (∫ ω, (∑ t ∈ range S,
      (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0)) ∂μ) ≤ (S : ℝ) * q := by
    rw [integral_finsetSum _ (by intro t ht; exact .of_finite)]
    have hsum := sum_le_sum (s := range S) fun t ht =>
      (parentDrawLaw_group_failure_mean R O M K count t (failure t)).trans_le (hfailure t (mem_range.mp ht))
    simpa only [sum_const, card_range, nsmul_eq_mul] using hsum
  rw [integral_add (.of_finite) (.of_finite), integral_add (.of_finite) (integrable_const _),
    integral_const, probReal_univ, one_smul, integral_const_mul, hprefixMean] at hmean
  have hfailureCost := mul_le_mul_of_nonneg_left hfailureMean hcharge
  nlinarith only [hmean, hprefix, hfailureCost]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementLocality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Locality of the complete physical refinement

Changing selection streams above a fixed level cannot alter histories at
that level or below. This proves the fixed-child environment under
parent-only resampling directly from the executable recurrence.
-/

namespace EditApproximation

/-- The complete history depends only on selection functions at its own
physical level and deeper levels. -/
theorem physicalRefinement_congr_from_level {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (d : ℕ) (hgroups : ∀ node, d ≤ node.1.val → first.groups node = second.groups node)
    (honline : ∀ node, d ≤ node.1.val → first.online node = second.online node)
    (node : PhysicalNode M J) (hnode : d ≤ node.1.val) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta first node t q =
      physicalRefinement source target U N P F A T delta second node t q := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_leaf source target U N P F A T delta first node hleaf,
        physicalRefinement_at_leaf source target U N P F A T delta second node hleaf]
    · have hchildren (i : Fin M) :
          physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i) =
            physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
        funext t q
        exact physicalRefinement_congr_from_level source target U N P F A T delta first second d hgroups honline
          (physicalChild node hbelow i) (by change d ≤ node.1.val + 1; omega) t q
      cases t with
      | zero =>
        rw [physicalRefinement_zero source target U N P F A T delta first,
          physicalRefinement_zero source target U N P F A T delta second]
      | succ t =>
        rw [physicalRefinement_succ source target U N P F A T delta first node hbelow hleaf,
          physicalRefinement_succ source target U N P F A T delta second node hbelow hleaf]
        simp only [hchildren, hgroups node hnode, honline node hnode]
  · have hlast : node.1.val = J := by have hbound := node.1.isLt; omega
    rw [physicalRefinement_at_last_level source target U N P F A T delta first node hlast,
      physicalRefinement_at_last_level source target U N P F A T delta second node hlast]
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

/-- Parent-only resampling fixes every child table, at every refinement
index and target state, without independence assumptions about children. -/
theorem physicalRefinement_children_fixed {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (first second : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hgroups : ∀ label, node.1.val < label.1.val → first.groups label = second.groups label)
    (honline : ∀ label, node.1.val < label.1.val → first.online label = second.online label) :
    (fun i : Fin M => physicalRefinement source target U N P F A T delta first (physicalChild node hbelow i)) =
      fun i : Fin M => physicalRefinement source target U N P F A T delta second (physicalChild node hbelow i) := by
  funext i t q
  apply physicalRefinement_congr_from_level source target U N P F A T delta first second (node.1.val + 1)
  · intro label hlabel
    exact hgroups label (by omega)
  · intro label hlabel
    exact honline label (by omega)
  · change node.1.val + 1 ≤ node.1.val + 1
    rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalResampledRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic first-crossing transfer under literal parent-only resampling. -/

namespace EditApproximation

open Finset

/-- A sampled regret at time t uses only the action sampled at that time. -/
theorem sampledPrefixRegret_current_sample_congr {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ) (clipped : ℕ → ℝ)
    (first second : ℕ → β → σ) (t : ℕ) (heq : first t = second t) :
    sampledPrefixRegret charge κ table clipped first t =
      sampledPrefixRegret charge κ table clipped second t := by
  simp only [sampledPrefixRegret, heq]

theorem physicalNode_resampled_regret {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (reference choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hM : 0 < M) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (hT : 0 < T)
    (hgroupsFixed : ∀ label, node.1.val < label.1.val → choices.groups label = reference.groups label)
    (honlineFixed : ∀ label, node.1.val < label.1.val → choices.online label = reference.online label)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
    (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target (physicalSourceInterval source.length node)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
    (q : TargetInterval target.length) (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
    (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈
      physicalNodeOnline source target U N P F A T delta choices node hbelow t q)
    (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta choices node hbelow t)
    (herror : 2 * gamma + 512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let history := physicalBandHistory source target U N P F A T delta reference node hbelow
    let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
    let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell t (draw t) gamma
    let crossing := firstCrossing specified.actions.toFinset S
      (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
    (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) - charge - clipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) + 2 * (delta : ℝ) * c +
          2 * (F : ℝ) * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  have hchildren := physicalRefinement_children_fixed source target U N P F A T delta
    choices reference node hbelow hgroupsFixed honlineFixed
  have hhistory : physicalBandHistory source target U N P F A T delta choices node hbelow =
      physicalBandHistory source target U N P F A T delta reference node hbelow := by
    funext t coordinate
    exact congrFun (congrFun (congrFun hchildren coordinate.1) t) coordinate.2
  have hselected' t :
      (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
        b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta choices node hbelow t := by
    simpa only [physicalNodeSelectedGroup, hhistory] using hselected t
  have hdet := physicalNode_firstCrossing_regret source target U N P F A T delta choices node hbelow
    hM hsize hP hF hA hseed hT hleaf b thetaExponent Q tau gamma κ htau hdelta hκ hκhalf
    cell hnonempty specified hspecified hrep q hb comparison hc sample hsample draw honline hselected' herror S
  have hclipped : physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison =
      physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison := by
    funext t
    simp only [physicalComparisonClipped, hhistory]
  have hfailure : physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell = physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell := by
    funext t draw gamma
    simp only [physicalNodeGroupFailure, hhistory]
  dsimp only at hdet ⊢
  rw [hhistory, hclipped, hfailure] at hdet
  exact hdet

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalConditionalNode
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.triangularChoiceWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional expected regret in a fixed child environment

Finite Bernstein bounds control the parent product draws. Agreement of
deeper selection functions fixes all child histories by locality, and
list membership connects the sampled actions to the refinement recurrence.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem physical_conditional_node_regret_oai {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P F b Q thetaExponent R H G K : ℕ}
    [NeZero M] [NeZero R] [NeZero (optimizerTriangularMass K)]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
    (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
    (hthetaeq : thetaExponent = 40 * smallLogExponent N) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
    (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta η κ : ℚ)
    (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (reference : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell ≠ [])
    (specified : UnskippedBand source target (physicalSourceInterval source.length node)
      b P thetaExponent (rationalParameters F).tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell)
    (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (hG : G = H + (bandCoordinates specified.actions.toFinset).card + 2) (hK : K = G ^ 80)
    (htau : 0 < (rationalParameters F).tau)
    (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
    (herror : 2 * (rationalParameters F).gamma +
      512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (realizations : BandParentSpace R M b F Q K → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (hgroupsFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).groups label = reference.groups label)
    (honlineFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).online label = reference.online label)
    (honlineWire : ∀ ω t, sharedBandRationalAction specified.center
      (physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
        b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t
          (parentOnlineDraw ω t)) ∈
      physicalNodeOnline source target U N P F A T delta (realizations ω) node hbelow t q)
    (hgroupWire : ∀ ω t,
      (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
        b thetaExponent Q (rationalParameters F).tau cell hnonempty t (parentGroupDraw ω t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta (realizations ω) node hbelow t)
    (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure)) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
    (∫ ω, (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ∂bandParentLaw R M b F Q K) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
  let history := physicalBandHistory source target U N P F A T delta reference node hbelow
  let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
  let sample := fun t integer => physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
    b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t integer
  let failure := fun t draw => physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
    b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma
  let crossing := firstCrossing specified.actions.toFinset S
    (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
  let prefixPayoff := fun t integer => sampledPrefixRegret charge (κ : ℝ)
    (fun t coordinate => (history t coordinate : ℝ)) clipped (fun j => sample j integer) t
  let regret := fun ω t => max c
    (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) - charge - clipped (t + 1)
  let budget := ((∑ child, specified.envelope child : ℚ) : ℝ) *
    (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) + (S : ℝ) / (H : ℝ) ^ 3)
  have hpoint (ω : BandParentSpace R M b F Q K) : (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range crossing, prefixPayoff t (parentOnlineDraw ω t)) + 2 * (delta : ℝ) * c +
        (2 * (F : ℝ) * c) * ∑ t ∈ range S, (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0) := by
    have hdet := physicalNode_resampled_regret source target U N P F A T delta
      reference (realizations ω) node hbelow hM hsize hP hF hA hseed hT
      (hgroupsFixed ω) (honlineFixed ω) hleaf b thetaExponent Q (rationalParameters F).tau
      (rationalParameters F).gamma κ htau hdelta hκ hκhalf cell hnonempty specified hspecified hrep q hb comparison hc
      (fun t => sample t (parentOnlineDraw ω t))
      (fun t => physicalBandOnlineDraw_mem source target U N P F A T delta reference node hbelow
        b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t (parentOnlineDraw ω t))
      (fun t => parentGroupDraw ω t) (honlineWire ω) (hgroupWire ω) herror S
    have hprefixEq : (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j)) t) =
        ∑ t ∈ range crossing, prefixPayoff t (parentOnlineDraw ω t) := by
      apply sum_congr rfl
      intro t _
      exact sampledPrefixRegret_current_sample_congr charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j))
        (fun j => sample j (parentOnlineDraw ω t)) t rfl
    change (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j)) t) + 2 * (delta : ℝ) * c +
        (2 * (F : ℝ) * c) * ∑ t ∈ range S,
          (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0) at hdet
    rw [hprefixEq] at hdet
    exact hdet
  have hprefix : (∑ t ∈ range crossing, uniformMean (prefixPayoff t)) ≤ budget := by
    exact physicalBand_prefix_expected_regret source target U N P F A T delta reference node hbelow
      b thetaExponent (rationalParameters F).tau specified.center hM hsize hP hF hA hseed hT htau hdelta.le
      specified.nonempty crossing S H G K (firstCrossing_le _ _ _ _) η κ hG hK comparison hc hH hη hκ hκhalf hηrange charge
  have hfailure t (_ht : t < S) :
      (groupSharedDrawLaw (M := M) (fun scale : Fin (groupDyadicScales M b F).length =>
        groupSampleCount M Q b (groupDyadicScaleAt M b F scale))).real {draw | failure t draw = true} ≤
          1 / (H : ℝ) ^ 4 := by
    rw [hHeq]
    exact physicalNode_groupFailure_probability source target N hN hell hM hMeq hPeq hFeq eb hbeq hQeq hthetaeq
      U A hsize hP hA hseed T hT delta reference node hbelow t cell bernstein
  have hbound := parentDrawLaw_firstCrossing_bound R (optimizerTriangularMass K) M
    (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) S crossing regret prefixPayoff failure
    budget (2 * (delta : ℝ) * c) (2 * (F : ℝ) * c) (1 / (H : ℝ) ^ 4)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg F))
      (Nat.cast_nonneg _)) hpoint hprefix hfailure
  dsimp only
  change (∫ ω, (∑ t ∈ range S, regret ω t) ∂bandParentLaw R M b F Q K) ≤
    budget + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c
  have hchargeEq : (2 * (F : ℝ) * c) * (S : ℝ) * (1 / (H : ℝ) ^ 4) =
      2 * S * (1 / (H : ℝ) ^ 4) * F * c := by ring
  exact hbound.trans_eq (by rw [hchargeEq])

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physical_conditional_node_regret_oai.{u_1} := @OAI.EditApproximation.physical_conditional_node_regret_oai.{u_1}
