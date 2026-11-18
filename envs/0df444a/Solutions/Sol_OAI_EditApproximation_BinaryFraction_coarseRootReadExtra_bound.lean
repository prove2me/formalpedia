-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:35.989692+00:00
-- url     : https://prove2.me/submissions/53d9a9ba-f998-4a23-bf7c-b24326763be5

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFixedDenominator
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact cache-value compression to a prescribed denominator.  It performs
one Boolean multiplication and one Boolean long division, followed only by
leading-zero removal.  No rational gcd or reduced-rational conversion is used. -/

namespace EditApproximation
namespace BinaryFraction

theorem raw_den_dvd_scaled_num (a : BinaryFraction) (D : ℕ) (hD : a.value.den ∣ D) :
    bitWordValue a.denominator ∣ bitWordValue a.numerator.bits * D := by
  have hd : (a.representation.den : ℤ) ≠ 0 := by exact_mod_cast a.representation.den_pos.ne'
  obtain ⟨c, hn, hd'⟩ := Rat.num_den_mk (q := a.value) (n := a.representation.num)
    (d := (a.representation.den : ℤ)) hd (by
      rw [Rat.divInt_eq_div, Int.cast_natCast]
      exact (representation_value a).symm)
  obtain ⟨k, hk⟩ := hD
  have hi : (a.representation.den : ℤ) ∣ a.representation.num * (D : ℤ) := by
    refine ⟨a.value.num * k, ?_⟩
    rw [hn, hd', hk, Nat.cast_mul]
    ring
  have habs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hi)
  have hnum : a.representation.num.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [representation, SignedBinary.value, signedMagnitude, h]
  change bitWordValue a.denominator ∣ (a.representation.num * (D : ℤ)).natAbs at habs
  simpa only [Int.natAbs_mul, Int.natAbs_natCast, hnum] using habs



theorem fixedDenominatorWithWork_value (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.value = a.value := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  have hdvd := raw_den_dvd_scaled_num a (bitWordValue denominator) hD
  have h := bitDivModWithWork_value a.denominator product.1 a.denominator_pos
  have hm : bitWordValue product.1 = bitWordValue a.numerator.bits * bitWordValue denominator :=
    bitMulWithWork_value _ _
  have hmod : bitWordValue quotient.2.1 = 0 := by
    have hz : bitWordValue product.1 % bitWordValue a.denominator = 0 := by
      rw [hm]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h.1, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hz
    simp only [Nat.mod_mod] at hz
    exact (Nat.mod_eq_of_lt h.2).symm.trans hz
  have hq : bitWordValue a.denominator * bitWordValue quotient.1 =
      bitWordValue a.numerator.bits * bitWordValue denominator := by
    have heq := h.1
    change bitWordValue product.1 = bitWordValue a.denominator * bitWordValue quotient.1 + bitWordValue quotient.2.1 at heq
    rw [hmod, Nat.add_zero] at heq
    exact heq.symm.trans hm
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hc : (canonicalizeWithWork raw).1.value = raw.value := by
    rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  change (canonicalizeWithWork raw).1.value = a.value
  rw [hc]
  have hdQ : (bitWordValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.denominator_pos.ne'
  have hDQ : (bitWordValue denominator : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hqQ : (bitWordValue a.denominator : ℚ) * bitWordValue quotient.1 =
      (bitWordValue a.numerator.bits : ℚ) * bitWordValue denominator := by exact_mod_cast hq
  cases hs : a.numerator.negative <;>
    simp only [raw, value, SignedBinary.value, signedMagnitude, hs, Bool.false_eq_true,
      ↓reduceIte, Int.cast_natCast, Int.cast_neg] <;>
    apply (div_eq_div_iff hDQ hdQ).mpr <;> nlinarith only [hqQ]

theorem fixedDenominatorWithWork_den (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.representation.den = bitWordValue denominator := by
  unfold fixedDenominatorWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSeed
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual bounded-shift coarse tree

Section 3's deterministic shift representation uses a complete finite
branching tree with empty/singleton source leaves. Bounded integer shifts
are encoded by `Fin (2k+1)`; code `k` is shift zero. Virtual target positions
are represented by fresh `none` symbols in a finite surrounding frame.
-/

namespace EditApproximation

open Finset EditDistortion

universe u



/-- The literal consecutive capacity chunks cover exactly the permitted
before; zero capacity and empty trailing chunks are included. -/
theorem coarse_capacity_chunks {α : Type u} (source : List α) (B capacity : ℕ) :
    (List.ofFn fun i : Fin B => (source.drop (i.val * capacity)).take capacity).flatten =
      source.take (B * capacity) := by
  induction B generalizing source with
  | zero => simp
  | succ B ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, zero_mul, List.drop_zero, Fin.val_succ]
    have hchunks : (List.ofFn fun i : Fin B =>
        (source.drop ((i.val + 1) * capacity)).take capacity) =
        List.ofFn (fun i : Fin B => ((source.drop capacity).drop (i.val * capacity)).take capacity) := by
      congr 1
      funext i
      simp only [List.drop_drop, Nat.add_mul, one_mul, Nat.add_comm]
    rw [hchunks, ih, ← List.take_add]
    simp only [Nat.succ_mul, Nat.add_comm]

/-- A concrete complete source tree with empty/singleton leaves. Its
recursive child chunks have the capacity prescribed by the remaining depth. -/


theorem coarseSourceTreeOfList_word {α : Type u} (B D : ℕ) (source : List α) :
    (coarseSourceTreeOfList B D source).word = source.take (B ^ D) := by
  induction D generalizing source with
  | zero => simp only [coarseSourceTreeOfList, CoarseSourceTree.word, pow_zero, List.take_one]
  | succ D ih =>
    simp only [coarseSourceTreeOfList, CoarseSourceTree.word, ih, List.take_take, min_self]
    rw [coarse_capacity_chunks, pow_succ, Nat.mul_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact common precision of the coarse recurrence

Minima and threshold maxima select existing rationals. All computed arrays
therefore share one denominator whose bit length grows linearly with depth.
-/

namespace EditApproximation

open Finset

universe u

theorem coarse_rat_mul_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hx : x.den ∣ common) : (x * n).den ∣ common := by
  have h := Rat.mul_den_dvd x (n : ℚ)
  simp only [Rat.den_natCast, mul_one] at h
  exact h.trans hx

theorem coarse_rat_div_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hn : 0 < n) (hx : x.den ∣ common) : (x / n).den ∣ common * n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_mul_inv]
  have h := Rat.mul_den_dvd x ((n : ℚ)⁻¹)
  simp only [Rat.den_inv_of_ne_zero hnq, Rat.num_natCast, Int.natAbs_natCast] at h
  exact h.trans (Nat.mul_dvd_mul hx (dvd_refl n))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridArithmetic
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact arithmetic on a shared coarse-array denominator. Addition touches
only the signed numerators and keeps the denominator, preventing denominator
growth across the child-array sums. All counters run Boolean primitives. -/

namespace EditApproximation
namespace BinaryFraction

/-- Store an integer on the common denominator by a literal bit product. -/


 theorem coarseGridNatWithWork_value (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.value = n := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  simp only [value, SignedBinary.value, signedMagnitude, Bool.false_eq_true, ↓reduceIte,
    bitMulWithWork_value, bitWordValue_bits]
  push_cast
  exact mul_div_cancel_right₀ _ (by exact_mod_cast hden.ne')

 theorem coarseGridNatWithWork_den (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.representation.den =
      bitWordValue denominator := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdArithmetic
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean threshold arithmetic on the fixed denominator of one coarse
execution. Quotients use actual long division when compressed to that grid. -/

namespace EditApproximation
namespace BinaryFraction



 theorem coarseDivideWithWork_value (a divisor : BinaryFraction)
    (hden : (a.value / divisor.value).den ∣ bitWordValue a.denominator) :
    (coarseDivideWithWork a divisor).1.value = a.value / divisor.value := by
  unfold coarseDivideWithWork
  dsimp only
  rw [fixedDenominatorWithWork_value, divWithWork_value]
  simpa only [divWithWork_value] using hden

 theorem coarseDivideWithWork_den (a divisor : BinaryFraction) :
    (coarseDivideWithWork a divisor).1.representation.den = a.representation.den := by
  exact fixedDenominatorWithWork_den _ _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Fresh-symbol right padding

Padding uses `none`, while original letters are tagged by `some`. Removing
the fresh symbols contracts every unrestricted unit-cost edit script.
-/

namespace EditApproximation

open EditDistortion

universe u v

/-- Right padding to a prescribed common width with a fresh tagged letter. -/


theorem coarsePadTo_length {α : Type u} (n : ℕ) (word : List α) (h : word.length ≤ n) :
    (coarsePadTo n word).length = n := by
  simp only [coarsePadTo, List.length_append, List.length_map, List.length_replicate]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- One descended allowance acquires only one factor of the fixed root
base in its denominator. This includes the literal sampled child label. -/
 theorem coarseChildAllowance_grid (B q L j : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ (j + 1) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  have heq : (1 / (L : ℚ)) * coarseChildThreshold B q allowance draw =
      coarseChildThreshold B q allowance draw / L := by ring
  rw [heq]
  convert coarse_rat_div_nat_den_dvd _ L _ hL ht using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGridTransfers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem coarseThreshold_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    (coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣ (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  apply ht.trans
  refine ⟨q * L * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

 theorem coarseChildAllowance_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  apply (coarseChildAllowance_grid B q L j allowance draw hB hq hL ha).trans
  refine ⟨q * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseThresholdStep
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Literal threshold numerator multiplication and denominator division.
The fixed-denominator quotient retains a root's common array grid. -/


private theorem coarseMultiply_nat_den (a : BinaryFraction) (n : ℕ) :
    (canonicalMulWithWork a (nat n)).1.representation.den = a.representation.den := by
  rw [canonicalMulWithWork_representation, nat_representation]
  simp only [UnreducedRational.mul, UnreducedRational.nat, mul_one]

 theorem coarseChildThresholdWithWork_value (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B)
    (hgrid : (coarseChildThreshold B q allowance.value draw).den ∣ allowance.representation.den) :
    (coarseChildThresholdWithWork B q allowance draw).1.value =
      coarseChildThreshold B q allowance.value draw := by
  unfold coarseChildThresholdWithWork
  dsimp only
  rw [coarseDivideWithWork_value]
  · simp only [canonicalMulWithWork_value, nat_value, coarseChildThreshold, Nat.cast_add,
      Nat.cast_one]
  · change Rat.den ((canonicalMulWithWork allowance (nat (draw.val + 1))).1.value /
      (canonicalMulWithWork (nat B) (nat q)).1.value) ∣
        (canonicalMulWithWork allowance (nat (draw.val + 1))).1.representation.den
    rw [coarseMultiply_nat_den]
    simpa only [canonicalMulWithWork_value, nat_value,
      coarseChildThreshold, Nat.cast_add, Nat.cast_one] using hgrid

 theorem coarseChildThresholdWithWork_den (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) :
    (coarseChildThresholdWithWork B q allowance draw).1.representation.den = allowance.representation.den := by
  exact (coarseDivideWithWork_den _ _).trans (coarseMultiply_nat_den allowance _)

/-- Local allowance division uses the same Boolean division and
compression primitive as threshold construction. -/


 theorem coarseChildAllowanceWithWork_value (L : ℕ) (threshold : BinaryFraction)
    (hgrid : (threshold.value / L).den ∣ threshold.representation.den) :
    (coarseChildAllowanceWithWork L threshold).1.value = threshold.value / L := by
  have hd : (threshold.value / (nat L).value).den ∣ bitWordValue threshold.denominator := by
    change (threshold.value / (nat L).value).den ∣ threshold.representation.den
    simpa only [nat_value] using hgrid
  simpa only [coarseChildAllowanceWithWork, nat_value] using
    coarseDivideWithWork_value threshold (nat L) hd

 theorem coarseChildAllowanceWithWork_den (L : ℕ) (threshold : BinaryFraction) :
    (coarseChildAllowanceWithWork L threshold).1.representation.den = threshold.representation.den :=
  coarseDivideWithWork_den _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseLabelWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Only expanded internal nodes request their child thresholds. The full
product seed is a specification; labels below a pruned node are never read. -/




private theorem coarseLabelChildren_le {B d : ℕ} {α : Type*} (Q lam allowance : ℚ)
    (labels arrays : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hle : ∀ child draw below, (child, draw, below) ∈ children → ∀ a, labels child below a ≤ arrays child below a) :
    coarseLabelChildren Q lam allowance labels children ≤
      coarseActiveChildrenWork Q lam allowance arrays children := by
  induction children with
  | nil => exact le_rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact Nat.add_le_add (hle child draw below List.mem_cons_self _)
      (ih (fun child draw below hmem => hle child draw below (List.mem_cons_of_mem _ hmem)))

 theorem coarseLabelCount_le_arrayWork {B d : ℕ} {α : Type*} (k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : ℚ) :
    coarseLabelCount Q lam tree draws allowance ≤ coarseActiveArrayWork k Q lam tree draws allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs <;> omega
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs
    · exact le_rfl
    · have hc := coarseLabelChildren_le Q lam allowance
        (fun child => coarseLabelCount Q lam child)
        (fun child => coarseActiveArrayWork k Q lam child)
        (List.ofFn fun i => (children i, draws i, below i)) (by
          intro child draw childBelow hmem a
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) a)
      have hunit : B ≤ B * (2 * k + 1) := by nlinarith
      exact Nat.add_le_add hunit hc

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseBinaryWeight
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseChildrenSpan_eq {B d : ℕ} {α : Type*}
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d)) :
    coarseChildrenSpan children = (children.map (fun data => data.1.word)).flatten.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    simp only [coarseChildrenSpan, List.map_cons, List.flatten_cons, List.length_append, ih]

 theorem coarseChildrenSpan_ofFn {B d : ℕ} {α : Type*}
    (children : Fin B → CoarseSourceTree B α d) (draws : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) :
    coarseChildrenSpan (List.ofFn fun i => (children i, draws i, below i)) =
      (CoarseSourceTree.branch children).word.length := by
  rw [coarseChildrenSpan_eq]
  simp only [List.map_ofFn, Function.comp_def, CoarseSourceTree.word]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarsePaddedRead_value {α : Type*} (n : ℕ) (word : List α) (hn : word.length ≤ n) (i : ℕ) :
    coarsePaddedRead n word i = (coarsePadTo n word)[i]? := by
  unfold coarsePaddedRead coarsePadTo
  by_cases hi : i < word.length
  · rw [ite_eq_left (hi.trans_le hn), List.getElem?_append_left (by simpa using hi),
      List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi), List.length_map,
      List.getElem?_replicate, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    by_cases hin : i < n
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarseReadTree_ext (B d : ℕ) {α : Type*} (read other : ℕ → Option α)
    (heq : ∀ i < B ^ d, read i = other i) :
    coarseReadTree B d read = coarseReadTree B d other := by
  induction d generalizing read other with
  | zero => exact congrArg CoarseSourceTree.leaf (heq 0 (by simp))
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    apply ih
    intro j hj
    apply heq
    rw [pow_succ]
    have hmul := Nat.mul_le_mul_right (B ^ d) (Nat.succ_le_of_lt i.isLt)
    have hpos : 0 < B ^ d := by omega
    nlinarith

theorem coarseReadTree_list (B d : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[i]?) = coarseSourceTreeOfList B d source := by
  induction d generalizing source with
  | zero => simp only [coarseReadTree, coarseSourceTreeOfList, List.head?_eq_getElem?]
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    rw [← ih]
    apply coarseReadTree_ext
    intro j hj
    simp only [List.getElem?_take_of_lt hj, List.getElem?_drop, Nat.add_comm]

theorem coarseReadTree_shift (B d start : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[start + i]?) =
      coarseSourceTreeOfList B d (source.drop start) := by
  rw [← coarseReadTree_list]
  congr 1
  funext i
  simp only [List.getElem?_drop]

theorem coarseReadTree_shift_length (B d start : ℕ) {α : Type*} (source : List α) :
    (coarseReadTree B d (fun i => source[start + i]?)).word.length =
      min (B ^ d) (source.length - start) := by
  rw [coarseReadTree_shift, coarseSourceTreeOfList_word, List.length_take, List.length_drop]

theorem coarseReadTree_padded_length (B d n start : ℕ) {α : Type*}
    (source : List α) (hn : source.length ≤ n) :
    (coarseReadTree B d (fun i => coarsePaddedRead n source (start + i))).word.length =
      coarseDescriptorLength B d n start := by
  have heq : (fun i => coarsePaddedRead n source (start + i)) =
      (fun i => (coarsePadTo n source)[start + i]?) := by
    funext i
    exact coarsePaddedRead_value n source hn _
  rw [heq, coarseReadTree_shift_length, coarsePadTo_length n source hn]
  rfl

theorem coarseReadTree_entry (B d : ℕ) {α : Type*} (source target : List α) :
    coarseReadTree B d (coarsePaddedRead (coarseEntryWidth source target) source) =
      coarseEntryTree B d source target := by
  have heq : coarsePaddedRead (coarseEntryWidth source target) source =
      (fun i => (coarsePadTo (coarseEntryWidth source target) source)[i]?) := by
    funext i
    exact coarsePaddedRead_value _ _ (le_max_left _ _) i
  rw [heq, coarseReadTree_list]
  rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseDescriptorWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Construct a descriptor's clipped length by Boolean exponentiation,
subtraction and minimum, retaining the resulting bits. -/


theorem coarseDescriptorWithWork_value (B d n start : ℕ) :
    bitWordValue (coarseDescriptorWithWork B d n start).1 = coarseDescriptorLength B d n start := by
  simp only [coarseDescriptorWithWork, wordMinWithWork_value,
    bitPowerWithWork_value, bitWordValue_bits, saturatingSubtractWithWork_value,
    coarseDescriptorLength]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseIndexSpan_eq {B d : ℕ} {α : Type*} (width : Fin B → ℕ)
    (children : Fin B → CoarseSourceTree B α d) (draw : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) (hw : ∀ i, width i = (children i).word.length)
    (indices : List (Fin B)) :
    coarseIndexSpan width indices =
      coarseChildrenSpan (indices.map fun i => (children i, draw i, below i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexSpan, List.map_cons, coarseChildrenSpan, hw, ih]

theorem coarseIndexWeight_eq {B d : ℕ} {α : Type*} (k q L : ℕ)
    (children : Fin B → CoarseSourceTree B α d) (draw : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) (allowance : BinaryFraction) (indices : List (Fin B)) :
    coarseIndexWeight q L draw (fun i => coarseBinaryWeight k q L (children i) (below i)) allowance indices =
      coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child) allowance
        (indices.map fun i => (children i, draw i, below i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexWeight, List.map_cons, coarseBinaryChildrenWeight, ih]

theorem coarseIndexAdditionalWork_bound {B : ℕ} (q L N C K : ℕ)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (extra : Fin B → BinaryFraction → ℕ → ℕ) (weight : Fin B → BinaryFraction → ℕ)
    (allowance : BinaryFraction) (indices : List (Fin B))
    (hc : ∀ i ∈ indices, ∀ s, s + width i ≤ N →
      extra i (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance (draw i)).1).1 s ≤
        C * weight i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draw i)).1).1 + K)
    (start : ℕ) (hstart : start + coarseIndexSpan width indices ≤ N) :
    coarseIndexAdditionalWork q L width draw extra allowance indices start ≤
      C * coarseIndexWeight q L draw weight allowance indices + K * indices.length := by
  induction indices generalizing start with
  | nil => simp only [coarseIndexAdditionalWork, coarseIndexWeight, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons i rest ih =>
    have hs : start + (width i + coarseIndexSpan width rest) ≤ N := hstart
    have hi := hc i List.mem_cons_self start (by omega)
    have hr := ih (fun j hj => hc j (List.mem_cons_of_mem i hj)) (start + width i) (by omega)
    simp only [coarseIndexAdditionalWork, coarseIndexWeight, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadAccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- A padded-source lookup tests its virtual endpoint and then reads the
original symbol array. Padding is represented by `none`. -/


theorem coarsePaddedReadWithWork_value {α : Type*} (n : ℕ) (source : List α) (offset : ℕ) :
    (coarsePaddedReadWithWork n source offset).1 = coarsePaddedRead n source offset := by
  unfold coarsePaddedReadWithWork coarsePaddedRead
  dsimp only
  simp only [binaryNaturalCompareWithWork_lt]

/-- Child offsets are formed by literal multiplication and addition. -/


theorem coarseChildOffsetWithWork_value (offset capacity index : ℕ) :
    bitWordValue (coarseChildOffsetWithWork offset capacity index).1 = offset + index * capacity := by
  simp only [coarseChildOffsetWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWeightSimulation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildrenWeight_eq {B d : ℕ} {α : Type*} (q L : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (arrays labels : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (allowance : BinaryFraction)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (he : ∀ child draw below, (child, draw, below) ∈ children →
      weight child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1 =
      arrays child below ((1 / L) * coarseChildThreshold B q allowance.value draw) +
      labels child below ((1 / L) * coarseChildThreshold B q allowance.value draw) + 1) :
    coarseBinaryChildrenWeight q L weight allowance children =
      coarseActiveChildrenWork q (1 / L) allowance.value arrays children +
      coarseLabelChildren q (1 / L) allowance.value labels children + children.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    rw [coarseBinaryChildrenWeight, he child draw below List.mem_cons_self,
      ih (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))]
    simp only [coarseActiveChildrenWork, coarseLabelChildren, List.length_cons]
    omega

 theorem coarseBinaryWeight_eq {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance =
      coarseActiveArrayWork k q (1 / L) tree draws allowance.value +
      coarseLabelCount q (1 / L) tree draws allowance.value + 1 := by
  induction tree generalizing j allowance with
  | leaf letter =>
    have hp := leWithWork_value (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.leaf (B := B) letter).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hp := leWithWork_value (nat (CoarseSourceTree.branch children).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
      have he : coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child)
          allowance (List.ofFn fun i => (children i, draws i, below i)) =
          coarseActiveChildrenWork q (1 / L) allowance.value
            (fun child => coarseActiveArrayWork k q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) +
          coarseLabelChildren q (1 / L) allowance.value
            (fun child => coarseLabelCount q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) + B := by
        refine (coarseBinaryChildrenWeight_eq q L (fun child => coarseBinaryWeight k q L child)
          (fun child => coarseActiveArrayWork k q (1 / L) child)
          (fun child => coarseLabelCount q (1 / L) child) allowance
          (List.ofFn fun i => (children i, draws i, below i)) ?_).trans ?_
        · intro child draw childBelow hmem
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          let threshold := (coarseChildThresholdWithWork B q allowance (draws i)).1
          let childAllowance := (coarseChildAllowanceWithWork L threshold).1
          have ht : threshold.value = coarseChildThreshold B q allowance.value (draws i) := by
            apply coarseChildThresholdWithWork_value
            rw [ha, ← hdepth]
            exact coarseThreshold_root_grid B q L j d allowance.value (draws i) hB hq hpath
          have htd : threshold.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildThresholdWithWork_den B q allowance (draws i)).trans ha
          have hcd : childAllowance.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildAllowanceWithWork_den L threshold).trans htd
          have hv : childAllowance.value = (1 / (L : ℚ)) *
              coarseChildThreshold B q allowance.value (draws i) := by
            have hg : (threshold.value / L).den ∣ threshold.representation.den := by
              rw [ht, htd, ← hdepth]
              rw [show coarseChildThreshold B q allowance.value (draws i) / (L : ℚ) =
                (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value (draws i) by ring]
              exact coarseChildAllowance_root_grid B q L j d allowance.value (draws i) hB hq hL hpath
            have hz := coarseChildAllowanceWithWork_value L threshold hg
            change childAllowance.value = _ at hz
            rw [hz, ht]
            ring
          have hcp : childAllowance.value.den ∣ (L * B * q) ^ (j + 1) := by
            rw [hv]
            exact coarseChildAllowance_grid B q L j allowance.value (draws i) hB hq hL hpath
          have hc := ih i (below i) (j + 1) (by omega) childAllowance hcd hcp
          rw [hv] at hc
          exact hc
        · simp only [List.length_ofFn]
      rw [he]
      omega

 theorem coarseBinaryWeight_le {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance ≤
      2 * coarseActiveArrayWork k q (1 / L) tree draws allowance.value + 1 := by
  rw [coarseBinaryWeight_eq k q L R tree draws hB hq hL j hdepth allowance ha hpath]
  have h := coarseLabelCount_le_arrayWork k (q : ℚ) (1 / L) tree draws allowance.value
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedOverhead
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedExtra coarseBinaryWeight

theorem coarseIndexedExtra_bound {B : ℕ} (R k q L n K : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (hB : 0 < B) (hK : 1 ≤ K)
    (hs : source.length ≤ n) (budget : CoarseReadBudget B R k n source target K)
    (d offset : ℕ) (draws : CoarseThresholdDraws B d) (allowance : BinaryFraction)
    (start : ℕ) (hd : d ≤ R) (hoff : offset + B ^ d ≤ B ^ R)
    (hstart : start + coarseDescriptorLength B d n offset ≤ n) :
    coarseIndexedExtra k q L n source target two d offset draws allowance start ≤
      (32 * K) * coarseBinaryWeight k q L
        (coarseReadTree B d (fun j => coarsePaddedRead n source (offset + j))) draws allowance := by
  induction d generalizing offset allowance start with
  | zero =>
    have ho : offset ≤ B ^ R := by omega
    have hdesc := budget.descriptor 0 hd offset ho
    have hread := budget.sourceRead offset ho
    have hsum : ((List.finRange (2 * k + 1)).map fun shift =>
        (coarseReadShiftWithWork k n target (coarsePaddedRead n source offset) start shift).2).sum ≤
        (2 * k + 1) * K := by
      calc
        _ ≤ ((List.finRange (2 * k + 1)).map fun _ => K).sum :=
          List.sum_le_sum (fun shift _ => budget.mismatch offset ho start (by omega) shift)
        _ = (2 * k + 1) * K := by simp
    have hlen := coarseReadTree_padded_length B 0 n offset source hs
    simp only [coarseReadTree, Nat.add_zero] at hlen ⊢
    rw [coarseIndexedExtra, coarseBinaryWeight, hlen]
    split_ifs
    · nlinarith only [hdesc, hK]
    · simp only [coarsePaddedReadWithWork_value]
      have hb : 2 * k + 1 ≤ B * (2 * k + 1) := Nat.le_mul_of_pos_left _ hB
      nlinarith only [hdesc, hread, hsum, hK, Nat.mul_le_mul_right K hb]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    have ho : offset ≤ B ^ R := by omega
    let children := fun i : Fin B => coarseReadTree B d
      (fun j => coarsePaddedRead n source (offset + i.val * B ^ d + j))
    let width := fun i : Fin B => coarseDescriptorLength B d n (offset + i.val * B ^ d)
    let weight := fun i : Fin B => coarseBinaryWeight k q L (children i) (below i)
    have htree : coarseReadTree B (d + 1) (fun j => coarsePaddedRead n source (offset + j)) =
        CoarseSourceTree.branch children := by
      simp only [coarseReadTree, children, Nat.add_assoc]
    have hlen : (CoarseSourceTree.branch children).word.length =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [← htree]
      exact coarseReadTree_padded_length B (d + 1) n offset source hs
    have hwidth (i : Fin B) : width i = (children i).word.length :=
      (coarseReadTree_padded_length B d n (offset + i.val * B ^ d) source hs).symm
    have hchild (i : Fin B) : offset + i.val * B ^ d + B ^ d ≤ B ^ R := by
      have hm := Nat.mul_le_mul_right (B ^ d) (Nat.succ_le_of_lt i.isLt)
      rw [pow_succ] at hoff
      nlinarith only [hm, hoff]
    let extra := fun i : Fin B => fun a s =>
      coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s +
        3 * ((coarseChildOffsetWithWork offset (B ^ d) i.val).2 +
          (coarseDescriptorWithWork B d n (offset + i.val * B ^ d)).2 +
          (binaryNaturalAddWithWork s (width i)).2 + 3)
    have hc : ∀ i ∈ List.finRange B, ∀ s, s + width i ≤ n →
        extra i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draws i)).1).1 s ≤
        (32 * K) * weight i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draws i)).1).1 + 18 * K := by
      intro i _ s hsi
      have hc := ih (offset + i.val * B ^ d) (below i)
        (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance (draws i)).1).1 s (by omega) (hchild i) hsi
      have h1 := budget.offset offset ho i d (by omega)
      have h2 := budget.descriptor d (by omega) (offset + i.val * B ^ d) (by have := hchild i; omega)
      have h3 := budget.advance s (by omega) (width i) (by omega)
      change _ ≤ (32 * K) * weight i _ at hc
      dsimp only [extra]
      omega
    have hspan : coarseIndexSpan width (List.finRange B) =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [coarseIndexSpan_eq width children draws below hwidth, ← List.ofFn_eq_map,
        coarseChildrenSpan_ofFn, hlen]
    have hloop := coarseIndexAdditionalWork_bound q L n (32 * K) (18 * K) width draws extra weight
      allowance (List.finRange B) hc start (by rw [hspan]; exact hstart)
    have hw := coarseIndexWeight_eq k q L children draws below allowance (List.finRange B)
    have hdesc := budget.descriptor (d + 1) hd offset ho
    have hpower := budget.power d (by omega)
    erw [htree, coarseIndexedExtra, coarseBinaryWeight, hlen]
    split_ifs
    · nlinarith only [hdesc, hK]
    · simp only [bitPowerWithWork_value, bitWordValue_bits, coarseChildOffsetWithWork_value,
        coarseDescriptorWithWork_value]
      change _ ≤ (32 * K) * (B * (2 * k + 1) + 1 + _)
      simp only [List.length_finRange] at hloop
      dsimp only [extra, width, weight] at hloop
      rw [hw, ← List.ofFn_eq_map] at hloop
      have hbase : 18 * K * B ≤ (32 * K) * (B * (2 * k + 1)) := by
        calc
          _ ≤ (32 * K) * B := by nlinarith only [Nat.zero_le (K * B)]
          _ ≤ _ := Nat.mul_le_mul_left (32 * K)
            (Nat.le_mul_of_pos_right B (by omega))
      nlinarith only [hloop, hdesc, hpower, hbase, hK]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseIndexedRootBound
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseRootReadExtra_bound_oai {B d : ℕ} (k q L K : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (hK : 1 ≤ K) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d)
    (budget : CoarseReadBudget B d k (coarseEntryWidth x y) x y K) :
    coarseRootReadExtra k q L hB hq hL x y draws ≤
      (32 * K) * (2 * coarseActiveArrayWork k q (1 / L)
        (coarseEntryTree B d x y) draws k + 1) := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  have he := coarseIndexedExtra_bound d k q L (coarseEntryWidth x y) K x y two.1 hB hK
    (le_max_left _ _) budget d 0 draws allowance.1 0 le_rfl (by omega)
    (by simp only [coarseDescriptorLength, Nat.sub_zero, Nat.zero_add]; exact min_le_right _ _)
  simp only [Nat.zero_add, coarseReadTree_entry] at he
  have ha : allowance.1.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ k).trans (coarseRootDenominator_value B q L d)
  have hv : allowance.1.value = k := coarseGridNatWithWork_value _ _ k
  have hp : allowance.1.value.den ∣ (L * B * q) ^ 0 := by
    rw [hv, Rat.den_natCast]
    exact one_dvd _
  have hw := coarseBinaryWeight_le k q L d (coarseEntryTree B d x y) draws hB hq hL
    0 (by omega) allowance.1 ha hp
  rw [hv] at hw
  change coarseIndexedExtra k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0 ≤ _
  exact he.trans (Nat.mul_le_mul_left (32 * K) hw)

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound_oai := @OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound_oai
