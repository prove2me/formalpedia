-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryMemoNormalized_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:02.039705+00:00
-- url     : https://prove2.me/submissions/b0bbba9a-3bc5-4899-8d9f-e184f5d48b13

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_queryFamilyMemoNormalized_width

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCanonicalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.denominatorInteger_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Removing only leading zero bits of an integer word. This is unrelated
to rational reduction: no common divisor is computed. -/

namespace EditApproximation



theorem trimBitWordWithWork_canonical (bits : List Bool) :
    (trimBitWordWithWork bits).1 = (bitWordValue bits).bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hzero : bitWordValue bits = 0
    · rw [trimBitWordWithWork, ih, hzero]
      cases bit <;> simp [bitWordValue, hzero]
    · have hnonempty : (bitWordValue bits).bits ≠ [] := by
        intro h
        have hv := bitWordValue_bits (bitWordValue bits)
        rw [h] at hv
        exact hzero hv.symm
      have hvalue : bitWordValue (bit :: bits) = Nat.bit bit (bitWordValue bits) := by
        cases bit <;> simp [bitWordValue, Nat.bit, Nat.add_comm]
      rw [trimBitWordWithWork, ih, ite_eq_right (by simp [hnonempty]), hvalue,
        Nat.bits_append_bit _ _ (fun h => False.elim (hzero h))]

theorem trimBitWordWithWork_length (bits : List Bool) :
    (trimBitWordWithWork bits).1.length = Nat.size (bitWordValue bits) := by
  rw [trimBitWordWithWork_canonical, Nat.size_eq_bits_len]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_sum_bit_length (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb : b < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [pow_succ]
  omega

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem refinementBaseWithWork_length (ell : List Bool) :
    (refinementBaseWithWork ell).1.length = Nat.size (bitWordValue ell ^ 10 + 1) := by
  simp only [refinementBaseWithWork, trimBitWordWithWork_length, bitAddWithWork_value,
    bitPowerWithWork_value, bitWordValue, Bool.toNat_true, Bool.toNat_false]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineParameters
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The two numerical constants used by online optimization are built from
the binary small-log parameter. Their word widths and construction costs
come from the actual multiplication loops. -/

namespace EditApproximation
namespace BinaryFraction



theorem onlineParametersWithWork_eta (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.1.value = (rationalParameters (bitWordValue ell)).eta := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

theorem onlineParametersWithWork_kappa (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.2.value = (rationalParameters (bitWordValue ell)).kappa := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundsAllSeeds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

 theorem stageInitial_upper_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (state : PhysicalEntry M J target.length) :
    stageInitial source target U N P F A state ≤ (32 * F + 1 : ℚ) * N := by
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf]
    have hcost : (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤ N := by
      exact_mod_cast physical_state_cost_le source target N hsize state
    change (stateEditCost (physicalSource source state.1) target state.2 : ℚ) ≤ _
    have hcoef : (1 : ℚ) ≤ 32 * F + 1 := by
      have hF : (0 : ℚ) ≤ F := Nat.cast_nonneg _
      linarith
    exact hcost.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℚ) N))
  · unfold localInitialConeTable
    split_ifs
    · positivity
    · exact rationalMinimum_le_fallback _ _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cell-keyed shared draws permit direct local group enumeration. The
complete and local finite programs use the same draw at every cell label. -/

namespace EditApproximation

theorem targetCell_of_cellTargetStates {n g : ℕ} {side : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (hside : 0 < side) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n g side cell) : targetCell side r = cell := by
  have hc := (cellTargetStates_mem cell hg r).mp hr
  apply Prod.ext
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.1⟩
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.2.2⟩

theorem chooseCellGroupAction_center {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell draw = some action) :
    action.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  exact (unskippedBandList_mem_iff _ _).mp
    (chooseUnskippedGroup_spec Q current _ hempty draw).1

theorem representativeCells_mem {n N P F b : ℕ} (a theta : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hr : (b, r) ∈ representativeList N P F a initial) :
    targetCell (theta * b) r ∈ representativeCells N P F b a theta initial := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  exact ⟨(b, r), List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩



section CellPrograms

variable {α : Type*} {M : ℕ} (source target : List α)
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q)

local notation "theta" => (2 : ℚ) ^ (-(exponent : ℤ))



theorem cellGroupAction_location (b : ℕ) (hb : b ∈ dyadicScales N) (cell : ℕ × ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell (draw b cell) = some action) :
    (b, action.center) ∈ representativeList N P F a parentInitial ∧
      targetCell (theta * b) action.center = cell := by
  have hcenter := chooseCellGroupAction_center source target parent b P F exponent Q tau a
    parentInitial child initial current cell (draw b cell) action hselected
  have hrep := cellRepresentativeStates_mem_representatives a parentInitial theta cell action.center hb hcenter
  have hbpos : 0 < b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    positivity
  have hcell := (List.mem_filter.mp hcenter).1
  exact ⟨hrep, targetCell_of_cellTargetStates cell (by unfold seedGridSpacing; omega)
    (by positivity) action.center hcell⟩

theorem localCellGroupActions_subset (q : TargetInterval target.length) :
    ∀ action ∈ localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q,
      action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  have hb' := (List.mem_filter.mp hb).1
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb' cell action hselected
  have hcell := representativeCells_mem a theta parentInitial action.center hlocation.1
  rw [hlocation.2] at hcell
  exact List.mem_flatMap.mpr ⟨b, hb', List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩⟩

theorem completeCellGroupActions_wide :
    ∀ action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw,
      action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  exact chooseCellGroupAction_wide_mem source target parent N b P F exponent Q tau a parentInitial
    child initial current cell (draw b cell) hb action hselected

end CellPrograms

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation




theorem dyadicSeedExponent_active (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    f < dyadicSeedExponent f initial pass := by
  have hd : 0 < f - 2 := by omega
  have hproduct : (f - 2) * pass < initial - f := by
    by_contra hn
    have hle : dyadicSeedPassCount f initial ≤ pass :=
      (ceilDiv_le_iff_le_mul hd).2 (le_of_not_gt hn)
    omega
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedExponent_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ f := by
  have hd : 0 < f - 2 := by omega
  have hproduct : initial - f ≤ (f - 2) * dyadicSeedPassCount f initial :=
    (ceilDiv_le_iff_le_mul hd).1 le_rfl
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedFactor_integer (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial pass) (2 ^ f) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
  have hactive := dyadicSeedExponent_active f initial pass hf hpass
  have hquotient : (2 : ℚ) ^ dyadicSeedExponent f initial pass / ((2 ^ f : ℕ) : ℚ) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
    push_cast
    apply (div_eq_iff (pow_ne_zero f (by norm_num : (2 : ℚ) ≠ 0))).2
    rw [← pow_add, Nat.sub_add_cancel hactive.le]
  unfold refinementFactor
  rw [hquotient, max_eq_right]
  exact_mod_cast Nat.one_le_two_pow (n := dyadicSeedExponent f initial pass - f)

theorem dyadicSeedFactor_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    (2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ (2 ^ f : ℕ) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (dyadicSeedExponent_terminal f initial hf)

theorem dyadicSeedFactor_terminal_refinement (f initial : ℕ) (hf : 3 ≤ f) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial)) (2 ^ f) = 1 := by
  unfold refinementFactor
  apply max_eq_left
  apply (div_le_one (by positivity : (0 : ℚ) < (2 ^ f : ℕ))).2
  exact dyadicSeedFactor_terminal f initial hf





end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalWideStep
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One concrete refinement entry, using direct local representative and
cell loops. Band data and previously gathered child tables are arguments;
no complete current-index child table is enumerated. -/

namespace EditApproximation

theorem rationalLocalWideStep_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) (hdelta : 0 ≤ delta) (hinitial : 0 ≤ parentInitial q)
    (hold : ∀ i r, 0 ≤ old i r) (hcurrent : ∀ i r, 0 ≤ current i r) :
    0 ≤ rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ∧
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ≤ parentInitial q := by
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun is => old is.1 is.2) q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
  let cone := rationalMinimum fallback
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (fun is => current is.1 is.2) q))
  have hfallback : 0 ≤ fallback := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hinitial, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action ha) (fun i => hold _ _)
  have hgroups : ∀ action ∈ groups, action ∈
      rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
    intro action ha
    exact completeCellGroupActions_wide source target parent N P F exponent Q tau a parentInitial
      childMass childInitial current draw action
      (localCellGroupActions_subset source target parent N P F exponent Q tau a parentInitial
        childMass childInitial current draw q action ha)
  have hcone : 0 ≤ cone := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hfallback, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action (hgroups action ha)) (fun i => hcurrent _ _)
  have hupper : cone ≤ parentInitial q := (rationalMinimum_le_fallback _ _).trans
    (rationalMinimum_le_fallback _ _)
  change 0 ≤ rationalRefinementUpdate delta cone _ ∧ rationalRefinementUpdate delta cone _ ≤ parentInitial q
  cases hmin : rationalOnlineMinimum (online.map
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => current is.1 is.2) q)) with
  | none => exact ⟨hcone, hupper⟩
  | some value =>
    exact ⟨le_min hcone ((div_nonneg hcone (by linarith)).trans (le_max_left _ _)),
      (min_le_left _ _).trans hupper⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal warmup can be calculated by direct bounded endpoint
loops. Equality with the complete tables is only asserted on good seeds;
the local rules themselves remain finite and bounded on every seed. -/

namespace EditApproximation

open Finset

theorem physicalLocalWarmup_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    0 ≤ physicalLocalWarmup source target U N P F A t state ∧
      physicalLocalWarmup source target U N P F A t state ≤ stageInitial source target U N P F A state := by
  induction t generalizing state with
  | zero => exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
  | succ t ih =>
    rw [physicalLocalWarmup]
    split_ifs
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
    · refine ⟨?_, rationalMinimum_le_fallback _ _⟩
      apply (le_rationalMinimum_iff _ _ _).2
      refine ⟨stageInitial_nonneg_all_seeds source target U N P F A state, ?_⟩
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      unfold rationalActionValue
      apply add_nonneg
      · exact add_nonneg (by positivity)
          (rationalActualWideActions_connection_nonneg _ _ _ action ha)
      · exact Finset.sum_nonneg (fun i _ => (ih _).1)
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local finite refinement recurrence, with direct query groups and
local warmup data. Current-index dependencies go only to physical children;
the recurrence is well founded before any accuracy assertion. -/

namespace EditApproximation

theorem physicalLocalRefinement_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ) (hdelta : 0 ≤ delta)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ∧
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ≤
        stageInitial source target U N P F A (node, q) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
  · cases t with
    | zero => exact physicalLocalWarmup_bounds source target U N P F A T (node, q)
    | succ t =>
      let children : PhysicalChildTables M target.length := fun i =>
        physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online
          (physicalChild node hbelow i)
      have hold (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i t r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) t r).1
      have hcurrent (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i (t + 1) r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) (t + 1) r).1
      exact rationalLocalWideStep_bounds source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (t + 1)) (online node children (t + 1) q) q hdelta
        (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hold hcurrent
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalValueBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit bit bounds for the actual returned physical table values. -/

namespace EditApproximation

theorem refinement_denominator_base_bits (ell : ℕ) :
    Nat.size (ell ^ 10 + 1) ≤ 10 * Nat.size ell + 3 := by
  have hsum := natural_sum_bit_length (ell ^ 10) 1
  have hpower := natural_power_bit_length ell 10
  norm_num only [Nat.size_one] at hsum
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCacheWords
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit multiword cache storage after substituting the computed height. -/

namespace EditApproximation

theorem cacheWordBudget_le_cube (H N F r B : ℕ) (hH : 64 ≤ H)
    (hN : Nat.size N ≤ H) (hF : F ≤ H) (hr : r ≤ H) (hB : B ≤ 13 * H) :
    Nat.size ((32 * F + 1) * N) + 2 * r * B + 3 ≤ H ^ 3 := by
  have hFsize : Nat.size F ≤ H := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hF
  have hm := natural_product_bit_length 32 F
  have ha := natural_sum_bit_length (32 * F) 1
  have hp := natural_product_bit_length (32 * F + 1) N
  have h32 : Nat.size 32 = 6 := by decide
  simp only [h32, Nat.size_one] at hm ha
  have hbits : Nat.size ((32 * F + 1) * N) ≤ 2 * H + 8 := by omega
  have hmul := Nat.mul_le_mul hr hB
  have hsquare : 2 * H + 11 ≤ H ^ 2 := by nlinarith
  have hcube := Nat.mul_le_mul_right (H ^ 2) hH
  have hc : 64 * H ^ 2 ≤ H ^ 3 := by
    simpa only [pow_succ'] using hcube
  nlinarith only [hbits, hmul, hsquare, hc, Nat.zero_le (H ^ 2)]

theorem computed_input_size_le_height (N : ℕ) : Nat.size N ≤ inputHeight N := by
  apply Nat.size_le.mpr
  exact (show N < N + 2 by omega).trans_le (inputHeight_covers_length N)

theorem computed_cacheWordBudget_le_cube (N r B : ℕ) (hH : 64 ≤ inputHeight N)
    (hr : r ≤ inputHeight N) (hB : B ≤ 10 * Nat.size (inputSmallLog N) + 3) :
    Nat.size ((32 * inputSmallLog N + 1) * N) + 2 * r * B + 3 ≤ inputHeight N ^ 3 := by
  apply cacheWordBudget_le_cube _ _ _ _ _ hH (computed_input_size_le_height N)
    (computed_smallLog_le_height N) hr
  have hs : Nat.size (inputSmallLog N) ≤ inputHeight N :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  omega

theorem computed_refinementBase_length (N : ℕ) (ell : List Bool)
    (hell : bitWordValue ell = inputSmallLog N) :
    (refinementBaseWithWork ell).1.length ≤ 10 * Nat.size (inputSmallLog N) + 3 := by
  rw [refinementBaseWithWork_length, hell]
  exact refinement_denominator_base_bits _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistorySemantic
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section History
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial
local notation "seed" pass => localSeedSequence source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial pass

theorem localRequestValue_bounds (hdelta : 0 ≤ delta) (request : PhysicalTableRequest M J target.length) :
    0 ≤ requestValue request ∧ requestValue request ≤
      stageInitial source target (seed request.pass) N P F (factor request.pass) (request.node, request.state) := by
  unfold localRequestValue unifiedPhysicalValue
  dsimp only
  split
  · exact physicalLocalWarmup_bounds source target _ N P F _ _ _
  · exact physicalLocalRefinement_bounds source target _ N P F exponent Q _ tau delta T hdelta _ _ _ _ _

end History
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite scalar family is exactly the accepted output of the
independent literal rejection samplers. Only requested coordinates need
be generated; their failure counts have a product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)





omit [NeZero M] in
 theorem physicalFamilyRange_bits_le (bits : ℕ)
    (hM : M ≤ 2 ^ bits) (hB : localOnlineMassBound M P H ≤ 2 ^ bits)
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    rejectionBitCount (physicalFamilyRange target N P F exponent H Q passes copies key) ≤ bits := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  rcases key with ⟨pass, copy, scalar, index⟩
  cases scalar with
  | inl online =>
    change online.2.val.val ≤ 2 ^ bits
    exact (Nat.le_of_lt_succ online.2.val.isLt).trans hB
  | inr group => exact hM

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computedFamilyRange_bits_le (source target : List ℕ) (N R : ℕ)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : ComputedFamilyScalarKey source target N R) :
    rejectionBitCount (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key) ≤ inputHeight N := by
  apply physicalFamilyRange_bits_le
  · change 2 ^ (heightExponent N / 20) ≤ 2 ^ inputHeight N
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    exact (Nat.div_le_self _ _).trans (Nat.lt_two_pow_self.le)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hB)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual finite adaptive sequence of median seed passes. Every chosen
incoming table uses its own fresh product of full-table copy streams. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem scheduledSeedMultiplier_spec (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass < computedSeedPassCount N) :
    (scheduledSeedMultiplier N pass : ℚ) = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) := by
  unfold scheduledSeedMultiplier scheduledSeedFactor
  simpa only [inputSmallLog] using
    (dyadicSeedFactor_integer (smallLogExponent N) (computedSeedInitialExponent N) pass hf hpass).symm

theorem scheduledSeedFactor_terminal_refinement (N : ℕ) (hf : 3 ≤ smallLogExponent N) :
    refinementFactor (scheduledSeedFactor N (computedSeedPassCount N)) (inputSmallLog N) = 1 := by
  exact dyadicSeedFactor_terminal_refinement (smallLogExponent N) (computedSeedInitialExponent N) hf

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRefinementWords
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The scheduled integer refinement factor is materialized by its dyadic
exponent; the terminal pass materializes one. -/


theorem scheduledRefinementWordWithWork_value (N pass : ℕ)
    (hf : 3 ≤ smallLogExponent N) (hpass : pass ≤ computedSeedPassCount N) :
    (scheduledRefinementWordWithWork N pass).1.value =
      refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) := by
  unfold scheduledRefinementWordWithWork
  split_ifs with h
  · simp only [BinaryFraction.signedPowerTwoWithWork_value, zpow_natCast]
    rw [← scheduledSeedMultiplier_spec N pass hf h]
    simp only [scheduledSeedMultiplier, Nat.cast_pow, Nat.cast_ofNat]
  · have heq : pass = computedSeedPassCount N := by omega
    rw [heq, scheduledSeedFactor_terminal_refinement N hf]
    exact BinaryFraction.nat_value 1



/-- Concrete construction of the scalar words consumed by the local kernel. -/


theorem refinementParameterWordsWithWork_values (N pass : ℕ) (word : List Bool)
    (hpositive : 0 < bitWordValue word) (hvalue : bitWordValue word = inputSmallLog N)
    (hf : 3 ≤ smallLogExponent N) (hpass : pass ≤ computedSeedPassCount N) :
    let values := (refinementParameterWordsWithWork N pass word hpositive).1
    values.tau.value = (rationalParameters (inputSmallLog N)).tau ∧
      values.factor.value = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) ∧
      values.eta.value = (rationalParameters (inputSmallLog N)).eta ∧
      values.kappa.value = (rationalParameters (inputSmallLog N)).kappa ∧
      values.delta.value = (rationalParameters (inputSmallLog N)).delta := by
  simp only [refinementParameterWordsWithWork, BinaryFraction.onlineParametersWithWork_kappa,
    BinaryFraction.onlineParametersWithWork_eta, BinaryFraction.refinementDecrementWithWork_value,
    scheduledRefinementWordWithWork_value N pass hf hpass, hvalue]
  simp [rationalParameters]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSeedWords
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The actual dyadic incoming approximation factor used by a seed pass. -/


theorem scheduledSeedWordWithWork_value (N pass : ℕ) :
    (scheduledSeedWordWithWork N pass).1.value = scheduledSeedFactor N pass := by
  simp only [scheduledSeedWordWithWork, BinaryFraction.signedPowerTwoWithWork_value,
    zpow_natCast, scheduledSeedFactor]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryCorrect
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryParameters_values (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass ≤ computedSeedPassCount N) :
    (computedQueryParameters N pass).tau.value = (rationalParameters (inputSmallLog N)).tau ∧
    (computedQueryParameters N pass).factor.value = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) ∧
    (computedQueryParameters N pass).eta.value = (rationalParameters (inputSmallLog N)).eta ∧
    (computedQueryParameters N pass).kappa.value = (rationalParameters (inputSmallLog N)).kappa ∧
    (computedQueryParameters N pass).delta.value = (rationalParameters (inputSmallLog N)).delta :=
  refinementParameterWordsWithWork_values N pass (inputSmallLog N).bits _ (bitWordValue_bits _) hf hpass

/-- Width of the actual stored word. -/
theorem computedQueryMemoNormalized_width_bound (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hf : 3 ≤ smallLogExponent N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) (V : ℕ)
    (hV : |computedFamilyExpectedValue source target N input key| ≤ (V : ℚ)) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).width ≤
      Nat.size V + 2 * (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key *
          (computedQueryBase N).length + 1) + 1 := by
  have hV' := hV
  simp only [computedFamilyExpectedValue] at hV'
  have hv := computedQueryParameters_values N 0 hf (Nat.zero_le _)
  have ha (pass : ℕ) (hpass : pass ≤ computedSeedPassCount N) :
      (computedQueryParameters N pass).factor.value =
        refinementFactor (scheduledSeedWordWithWork N pass).1.value (inputSmallLog N) := by
    rw [scheduledSeedWordWithWork_value]
    exact (computedQueryParameters_values N pass hf hpass).2.1
  have hd : (computedQueryParameters N 0).delta.value = 1 / (inputSmallLog N : ℚ) ^ 10 := hv.2.2.2.2
  have h := queryFamilyMemoNormalized_width source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0)) input.2
    (clampedSeedNat input.1) ha hs ht hp htable (fun entry => BinaryFraction.nat_value _)
    (inputSmallLog N) (Nat.two_pow_pos _) hd (computedQueryBase N) (computedQueryBase_value N) key (computedQueryBase N).length V le_rfl (by
      simp only [SourceRanked.value, scheduledSeedWordWithWork_value,
        hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
      exact hV')
  simp only [computedQueryMemoNormalized] at h ⊢
  exact h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryWidth
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Uniform magnitude bound for every table, independently of accuracy. -/
theorem computedFamilyTableValue_abs_le (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyTableKey source target N) :
    |computedFamilyTableValue source target N input key| ≤ (((32 * inputSmallLog N + 1) * N : ℕ) : ℚ) := by
  cases key with
  | inl entry =>
    change |(clampedSeedNat input.1 entry : ℚ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (show clampedSeedNat input.1 entry ≤ (32 * inputSmallLog N + 1) * N from
      (Nat.le_of_lt_succ (input.1 entry).isLt).trans (by nlinarith))
  | inr request =>
    unfold computedFamilyTableValue physicalFamilyRequestValue chargedRequestValue
    have hb := localRequestValue_bounds (R := inputHeight N ^ 2) source target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (integerParameters N).T (integerParameters N).S (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N)
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
      (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
      (physicalFamilyGroup target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) input.2)
      (physicalFamilyInteger source target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (integerParameters N).T
        (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N)
        (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
        (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
        (computedParameterP_pos N) input.2 (clampedSeedNat input.1))
      (clampedSeedNat input.1) (by change 0 ≤ 1 / (inputSmallLog N : ℚ) ^ 10; positivity) request.val
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans (by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        stageInitial_upper_all_seeds source target _ N (integerParameters N).P (inputSmallLog N)
          (scheduledSeedFactor N request.val.pass) hsize (request.val.node, request.val.state))

theorem computedQueryMemoNormalized_width_oai (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).width ≤
        inputHeight N ^ 3 := by
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hbase := computed_refinementBase_length N (inputSmallLog N).bits (bitWordValue_bits _)
  change (computedQueryBase N).length ≤ 10 * Nat.size (inputSmallLog N) + 3 at hbase
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hell
    nlinarith only [h, hell]
  cases key with
  | inl key =>
    have hr := computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hMass key
    have hc : (input.2 key).val < 2 ^ inputHeight N := (input.2 key).isLt.trans_le
      ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hr))
    have hv : |computedFamilyExpectedValue source target N input (.inl key)| ≤
        ((2 ^ inputHeight N : ℕ) : ℚ) := by
      change |((input.2 key).val : ℚ)| ≤ _
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hc.le
    have hw := computedQueryMemoNormalized_width_bound source target N occurrence symbolBits positionBits
      input hf hs ht hp htable (.inl key) (2 ^ inputHeight N) hv
    simp only [queryFamilyMemoRemaining, Nat.zero_mul, Nat.zero_add, Nat.mul_one,
      Nat.size_pow] at hw
    have hsquare : inputHeight N + 4 ≤ inputHeight N ^ 2 := by nlinarith only [hH]
    have hcub := hsquare.trans (Nat.pow_le_pow_right (by omega : 0 < inputHeight N) (by decide : 2 ≤ 3))
    omega
  | inr key =>
    have hw := computedQueryMemoNormalized_width_bound source target N occurrence symbolBits positionBits
      input hf hs ht hp htable (.inr key) ((32 * inputSmallLog N + 1) * N)
      (computedFamilyTableValue_abs_le source target N hsize input key)
    have hr : queryFamilyMemoRemaining (R := inputHeight N ^ 2) target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (.inr key) ≤ inputHeight N := by
      cases key with
      | inl entry => exact Nat.zero_le _
      | inr request => exact (Nat.sub_le _ _).trans hJ
    have hm := Nat.mul_le_mul_right (computedQueryBase N).length hr
    have hb := computed_cacheWordBudget_le_cube N (inputHeight N) (computedQueryBase N).length hH le_rfl hbase
    simp only [Nat.mul_assoc] at hb
    omega

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryMemoNormalized_width_oai := @OAI.EditApproximation.computedQueryMemoNormalized_width_oai
