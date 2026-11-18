-- Prove2me | solution 1 for OAI.EditApproximation.unskipped_expected_regret_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:28.485684+00:00
-- url     : https://prove2.me/submissions/8bcde097-0a46-4039-84d4-8b379bebf11b

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea002

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandDimension
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension charged by entropy is the number of actual child coordinates. -/

namespace EditApproximation

open Finset

theorem computed_band_dimension_log (N : ℕ) (hN : 0 < N)
    (hell : 42 ≤ inputSmallLog N) {nx ny b : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (band : List (Fin (integerParameters N).M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList (integerParameters N).M parent r b (integerParameters N).P) :
    Real.log (bandCoordinates band.toFinset).card ≤
      4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ) := by
  let ell := inputSmallLog N
  let p := coarseExponent ell
  let H := inputHeight N
  let P := (integerParameters N).P
  let M := (integerParameters N).M
  let d := (bandCoordinates band.toFinset).card
  have hellR : (42 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hPpos : 0 < P := pow_pos (Nat.two_pow_pos (heightExponent N)) _
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hPpos
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMexp : (M : ℝ) ≤ Real.exp ell :=
    (show (M : ℝ) ≤ H by exact_mod_cast hM).trans (computed_height_exp_upper N hN)
  have hPexp : (P : ℝ) ≤ Real.exp (((p : ℝ) + 20) * ell) := by
    change ((H ^ (p + 20) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_pow]
    have h := pow_le_pow_left₀ (Nat.cast_nonneg H) (computed_height_exp_upper N hN) (p + 20)
    rw [← Real.exp_nat_mul] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have h42 : (42 : ℝ) ≤ Real.exp ell := by linarith only [Real.add_one_le_exp (ell : ℝ), hellR]
  have hbox : (40 * P + 2 : ℝ) ≤ Real.exp (((p : ℝ) + 21) * ell) := by
    calc
      (40 * P + 2 : ℝ) ≤ 42 * P := by linarith only [hPone]
      _ ≤ Real.exp ell * Real.exp (((p : ℝ) + 20) * ell) :=
        mul_le_mul h42 hPexp (Nat.cast_nonneg P) (Real.exp_pos _).le
      _ = Real.exp (((p : ℝ) + 21) * ell) := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (d : ℝ) ≤ M * (40 * P + 2 : ℝ) ^ 2 := by
    exact_mod_cast bandCoordinates_card_le parent r hPpos band hband
  have hexp : (d : ℝ) ≤ Real.exp (4 * ((p : ℝ) + 21) * ell) := by
    apply hcount.trans
    have h := mul_le_mul hMexp (pow_le_pow_left₀ (by positivity) hbox 2) (by positivity)
      (Real.exp_pos _).le
    apply h.trans
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat]
    apply Real.exp_le_exp.mpr
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hp hell0, hell0]
  by_cases hd : d = 0
  · change Real.log (d : ℝ) ≤ _
    rw [hd, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have hlog := (Real.log_le_iff_le_exp hdR).2 hexp
    simpa only [p, ell, d, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hlog

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_UnskippedRegretBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual guarded band supplies the mass and entropy factors in the node budget. -/

namespace EditApproximation

open Finset

theorem band_dimension_log_of_computed (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N)
    {nx ny M b P : ℕ} (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
    (parent : TargetInterval nx) (r : TargetInterval ny) (band : List (Fin M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList M parent r b P) :
    Real.log (bandCoordinates band.toFinset).card ≤
      4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ) := by
  subst M P
  exact computed_band_dimension_log N hN hell parent r band hband

theorem unskipped_expected_regret_budget_oai {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N) {M b P thetaExponent : ℕ}
    (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
    (parent : TargetInterval source.length) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hF : 0 ≤ F) (c : ℝ) (hb : (b : ℝ) ≤ c)
    (eta kappa delta : ℚ) (heta : 0 < eta) (hkappa : 0 ≤ kappa) (S H : ℕ) :
    ((∑ i, member.envelope i : ℚ) : ℝ) *
        (Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) + 2 * (kappa : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c ≤
      (64 * (F : ℝ) *
        ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
          2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F) * c := by
  have hlog := band_dimension_log_of_computed N hN hell hMeq hPeq parent member.center member.actions
    (fun action ha => representativeBandActions_wide source target parent member.center b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child action ha)
  have hmass : (0 : ℝ) ≤ ((∑ i, member.envelope i : ℚ) : ℝ) := by
    exact (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun i _ => (bandChildEnvelope_pos _ _ _ _).le)
  have hmassBound : ((∑ i, member.envelope i : ℚ) : ℝ) ≤ 64 * (F : ℝ) * c := by
    have hQ := (Rat.cast_le (K := ℝ)).mpr member.sum_guard
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at hQ
    have hFR := (Rat.cast_nonneg (K := ℝ)).mpr hF
    simpa only [UnskippedBand.envelope, UnskippedBand.actions, Rat.cast_sum] using
      hQ.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) hFR))
  let upper : ℝ := (4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
    2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3
  have hupper : 0 ≤ upper := by
    exact add_nonneg (add_nonneg (div_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      ((Rat.cast_pos (K := ℝ)).mpr heta).le) (mul_nonneg (by norm_num) ((Rat.cast_nonneg (K := ℝ)).mpr hkappa)))
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3))
  have hbracket : Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) +
      2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3 ≤ upper := by
    dsimp only [upper]
    exact add_le_add_left (add_le_add_left
      (div_le_div_of_nonneg_right hlog ((Rat.cast_pos (K := ℝ)).mpr heta).le) _) _
  have hprod := (mul_le_mul_of_nonneg_left hbracket hmass).trans
    (mul_le_mul_of_nonneg_right hmassBound hupper)
  dsimp only [upper] at hprod
  nlinarith only [hprod]

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.unskipped_expected_regret_budget_oai.{u_1} := @OAI.EditApproximation.unskipped_expected_regret_budget_oai.{u_1}
