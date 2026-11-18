-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:36:58.630194+00:00
-- url     : https://prove2.me/submissions/8dba2066-52ff-4fee-84eb-879a8abe2674

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











theorem lookup_insert_other (tree : BinaryMemo α) (key query : List Bool) (a : α)
    (hne : query ≠ key) : (tree.insert key a).lookup query = tree.lookup query := by
  induction key generalizing tree query with
  | nil =>
    cases query with
    | nil => exact False.elim (hne rfl)
    | cons b rest => cases b <;> rfl
  | cons b rest ih =>
    cases query with
    | nil => cases b <;> rfl
    | cons c tail =>
      cases b <;> cases c
      · exact ih tree.left tail (fun h => hne (congrArg (List.cons false) h))
      · rfl
      · rfl
      · exact ih tree.right tail (fun h => hne (congrArg (List.cons true) h))

/-- Persistent insertion allocates one new node at each visited level;
the two untouched subtrees are retained by pointer. -/


theorem insertCosted_spec (tree : BinaryMemo α) (key : List Bool) (a : α) :
    tree.insertCosted key a = (tree.insert key a, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [insertCosted, insert, ih, List.length_cons]

end BinaryMemo

theorem binaryMemoKey_injective (d : ℕ) :
    Set.InjOn (binaryMemoKey d) {n | n < 2 ^ d} := by
  induction d with
  | zero => intro n hn m hm _; simp only [pow_zero, Set.mem_ofPred_eq] at hn hm; omega
  | succ d ih =>
    intro n hn m hm heq
    have hpair := List.cons.inj heq
    have hmod : n % 2 = m % 2 := by
      have hiff := decide_eq_decide.mp hpair.1
      omega
    have hnq : n / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hn
      omega
    have hmq : m / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hm
      omega
    have hquot := ih hnq hmq hpair.2
    omega

theorem binaryMemo_lookup_insert {α : Type*} (tree : BinaryMemo α)
    (d key query : ℕ) (hkey : key < 2 ^ d) (hquery : query < 2 ^ d) (a : α) :
    (tree.insert (binaryMemoKey d key) a).lookup (binaryMemoKey d query) =
      if query = key then some a else tree.lookup (binaryMemoKey d query) := by
  split_ifs with heq
  · subst query
    exact BinaryMemo.lookup_insert_same _ _ _
  · apply BinaryMemo.lookup_insert_other
    intro hencoded
    exact heq (binaryMemoKey_injective d hquery hkey hencoded)

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

theorem coarseSourceTreeOfList_word_eq {α : Type u} (B D : ℕ) (source : List α)
    (hcapacity : source.length ≤ B ^ D) :
    (coarseSourceTreeOfList B D source).word = source := by
  rw [coarseSourceTreeOfList_word, List.take_of_length_le hcapacity]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The concrete pruned coarse estimator

The random labels are a finite complete tree of integers in `1,...,B`.
Every execution below uses rational arithmetic and literal finite minima;
pruned arrays are represented by the zero function. Accuracy events are
kept separate from this executable definition.
-/

namespace EditApproximation

open Finset

universe u

/- All threshold labels, including labels below nodes which may be pruned. -/


theorem coarseChildThreshold_pos {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 < Q) (ha : 0 < allowance) : 0 < coarseChildThreshold B Q allowance draw := by
  have hB : 0 < B := Nat.zero_lt_of_lt draw.isLt
  unfold coarseChildThreshold
  positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem ceilDiv_comp (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a * b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb), Nat.mul_assoc]

theorem balanced_child_width_le_ceiling (width M i : ℕ) (hM : 0 < M) :
    ((i + 1) * width / M) - i * width / M ≤ width ⌈/⌉ M := by
  let c := width ⌈/⌉ M
  have hceil : width ≤ M * c := (ceilDiv_le_iff_le_mul hM).mp (le_refl c)
  have hfloor := Nat.lt_mul_div_succ (i * width) hM
  have hsum : i * width + width < (i * width / M + c + 1) * M := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul hM).2 hsum
  have hid : (i + 1) * width = i * width + width := by ring
  rw [hid]
  omega

theorem sourceChild_width_le_ceiling {n M : ℕ} (parent : TargetInterval n) (child : Fin M) :
    (sourceChild parent child).hi - (sourceChild parent child).lo ≤
      (parent.hi - parent.lo) ⌈/⌉ M := by
  dsimp only [sourceChild, balancedCut]
  rw [Nat.add_sub_add_left]
  exact balanced_child_width_le_ceiling _ _ _ (Nat.zero_lt_of_lt child.isLt)

theorem sourceIntervalAt_width (M n d : ℕ) (hM : 0 < M) (node : TreeLayer M d) :
    (sourceIntervalAt M n d node).hi - (sourceIntervalAt M n d node).lo ≤ n ⌈/⌉ M ^ d := by
  induction d with
  | zero => simp [sourceIntervalAt]
  | succ d ih =>
    have hchild := sourceChild_width_le_ceiling (sourceIntervalAt M n d node.1) node.2
    have hmono := (gc_mul_ceilDiv hM).monotone_l (ih node.1)
    have hcomp := ceilDiv_comp n (M ^ d) M (pow_pos hM d) hM
    change (sourceChild (sourceIntervalAt M n d node.1) node.2).hi -
        (sourceChild (sourceIntervalAt M n d node.1) node.2).lo ≤ n ⌈/⌉ M ^ (d + 1)
    exact hchild.trans (hmono.trans_eq (by rw [hcomp, pow_succ]))

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

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSampling
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSampling
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent heterogeneous coarse threshold samples

Every child has its own fixed true cost and an independent uniform label
in `1,...,B`. The child estimates are absent from this probability space:
they enter only the pathwise reconstruction proved separately.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem coarse_sum_labels (B : ℕ) (value : ℕ → ℝ) :
    (∑ draw : Fin B, value (draw.val + 1)) = ∑ r ∈ Icc 1 B, value r := by
  refine sum_bij (fun draw _ => draw.val + 1) ?_ ?_ ?_ ?_
  · intro draw hdraw
    exact mem_Icc.mpr ⟨by omega, by have := draw.isLt; omega⟩
  · intro first hfirst second hsecond hequal
    exact Fin.ext (by omega)
  · intro r hr
    obtain ⟨hlower, hupper⟩ := mem_Icc.mp hr
    refine ⟨⟨r - 1, by omega⟩, mem_univ _, ?_⟩
    change r - 1 + 1 = r
    omega
  · intro draw hdraw
    rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitial
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u

theorem coarseEntryTree_word {α : Type u} (B D : ℕ) (x y : List α)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) :
    (coarseEntryTree B D x y).word = coarsePadTo (coarseEntryWidth x y) x := by
  apply coarseSourceTreeOfList_word_eq
  rw [coarsePadTo_length _ _ (le_max_left _ _)]
  exact hcapacity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Computed numerical premises of the initial seed

The literal dyadic estimator uses the input-computed branching factor,
threshold and precision. Its depth and distortion bounds follow from
those integer parameters.
-/

namespace EditApproximation





theorem computed_coarse_branching (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    4 ≤ inputHeight N ∧ inputHeight N ≤ (integerParameters N).B := by
  have hlogs := inputSmallLog_bounds N hN
  have hexp : 2 ≤ heightExponent N := by omega
  have hH : 4 ≤ inputHeight N := by
    change 2 ^ 2 ≤ 2 ^ heightExponent N
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hexp
  have hlog : 1 ^ 4 ≤ Nat.log 2 (inputSmallLog N) := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    norm_num
    omega
  have hp := coarseExponent_maximal (inputSmallLog N) 1 hlog
  have hB : inputHeight N ≤ inputHeight N ^ coarseExponent (inputSmallLog N) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ inputHeight N) hp
  exact ⟨hH, hB⟩

theorem computed_coarse_depth (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    n ≤ (integerParameters N).B ^ computedCoarseDepth N n ∧
      computedCoarseDepth N n ≤ inputHeight N := by
  have hB := computed_coarse_branching N hN hell
  have hBtwo : 2 ≤ (integerParameters N).B := by omega
  constructor
  · exact (le_max_right 1 n).trans (Nat.le_pow_clog hBtwo (max 1 n))
  · have hanti := Nat.clog_anti_left (by decide : 1 < 2) hBtwo (n := max 1 n)
    have hlength : max 1 n ≤ 2 ^ inputHeight N := by
      apply max_le Nat.one_le_two_pow
      exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    exact hanti.trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoizedOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent dictionary requests. A fresh oracle is called only on a
cache miss; subsequent requests preserve and return the stored answer. -/

namespace EditApproximation

section Requests

variable {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (oracle : ι → ℚ)

theorem memoSound_empty : memoSound bits encode oracle .empty := by
  intro key value hvalue
  rw [BinaryMemo.lookup_empty] at hvalue
  cases hvalue

end Requests

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Well-founded recursive memo evaluation. A local query program may
choose later requests from earlier answers. Each recursive request carries
its strict rank decrease; no complete table is evaluated in advance. -/

namespace EditApproximation





namespace FiniteQuery



theorem run_sound {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
        memoSound bits encode expected (ask key memory).memory)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    (run ask program memory).value = program.value answer ∧
      memoSound bits encode expected (run ask program memory).memory := by
  induction program generalizing memory with
  | done result => exact ⟨rfl, hsound⟩
  | read key next ih =>
    have hfirst := hask key memory hsound
    have hrest := ih (ask key memory).value (ask key memory).memory hfirst.2
    refine ⟨?_, hrest.2⟩
    simpa only [run, value, hfirst.1] using hrest.1

end FiniteQuery



theorem memoSound_insert {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (expected : κ → ℚ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) (key : κ) :
    memoSound bits encode expected
      (memory.insert (binaryMemoKey bits (encode key)) (expected key)) := by
  intro other result hresult
  rw [binaryMemo_lookup_insert _ bits (encode key) (encode other)
    (hbounded key) (hbounded other)] at hresult
  split_ifs at hresult with heq
  · have hkey : other = key := hinjective heq
    subst other
    exact Option.some.inj hresult.symm
  · exact hsound other result hresult

theorem rankedMemoEvaluate_sound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    (rankedMemoEvaluate rank program bits encode key memory).value = rankedProgramValue rank program key ∧
      memoSound bits encode (rankedProgramValue rank program)
        (rankedMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      (rankedMemoEvaluate rank program bits encode key memory).value = rankedProgramValue rank program key ∧
        memoSound bits encode (rankedProgramValue rank program)
          (rankedMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · rename_i result hresult
        exact ⟨hmemory key result hresult, hmemory⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
              memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hprevious
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hprevious
        have hrun := FiniteQuery.run_sound bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        have hvalue : (FiniteQuery.run
            (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedProgramValue rank program key := by
          rw [rankedProgramValue]
          exact hrun.1
        simp only [BinaryMemo.insertCosted_spec]
        refine ⟨hvalue, ?_⟩
        rw [hvalue]
        exact memoSound_insert bits encode hinjective hbounded _ _ hrun.2 key
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_eq_sum {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) :
    program.cost oracle weight = ((program.keys oracle).map weight).sum := by
  induction program with
  | done _ => rfl
  | read key next ih => exact congrArg (weight key + ·) (ih (oracle key))

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FreshCoordinateCost
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A first request can depend on earlier answers, but cannot depend on
its own unexposed coordinate. Finite product independence then preserves
that coordinate's unconditional expected cost. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory Finset

attribute [local instance] Classical.propDecidable



namespace FiniteQuery

/-- Changing an oracle only at `key` does not change whether `key` is
requested. The two executions agree up to its first request. -/
theorem mem_keys_iff_of_agree_off {ι : Type*} [DecidableEq ι]
    (left right : ι → ℚ) (key : ι)
    (hagrees : ∀ other, other ≠ key → left other = right other)
    (query : FiniteQuery ι) : key ∈ query.keys left ↔ key ∈ query.keys right := by
  induction query with
  | done value => rfl
  | read first next ih =>
    by_cases heq : first = key
    · subst first
      simp only [keys, List.mem_cons, true_or]
    · have hvalue := hagrees first heq
      simp only [keys, List.mem_cons, Ne.symm heq, false_or, hvalue]
      exact ih (right first)

end FiniteQuery

theorem sum_distinct_requests_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, if i ∈ keys then weight i else 0) ≤ (keys.map weight).sum := by
  have hset : univ.filter (fun i => i ∈ keys) = keys.toFinset := by ext i; simp
  rw [← sum_filter, hset]
  clear hset
  induction keys with
  | nil => simp
  | cons key keys ih =>
    by_cases hmem : key ∈ keys
    · simp only [List.toFinset_cons, insert_eq_of_mem (List.mem_toFinset.mpr hmem),
        List.map_cons, List.sum_cons]
      omega
    · rw [List.toFinset_cons, sum_insert (by simpa only [List.mem_toFinset] using hmem),
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

theorem sum_selected_nat_weights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, selectionIndicator (i ∈ keys) * (weight i : ℝ)) ≤
      ((keys.map weight).sum : ℕ) := by
  calc
    _ = ∑ i, if i ∈ keys then (weight i : ℝ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ keys <;> simp [selectionIndicator, hi]
    _ ≤ _ := by exact_mod_cast sum_distinct_requests_le keys weight

section IndependentCost

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Selection stable under replacing its own coordinate is independent
of that coordinate. No accuracy event is used. -/
theorem fresh_coordinate_independent (i : ι) (selected : (∀ j, X j) → Prop)
    (hstable : ∀ left right : ∀ j, X j,
      (∀ j, j ≠ i → left j = right j) → (selected left ↔ selected right))
    (cost : X i → ℝ) :
    IndepFun (fun draw => selectionIndicator (selected draw))
      (fun draw => cost (draw i)) (Measure.pi μ) := by
  classical
  let S : Finset ι := univ.erase i
  let restore : (∀ j : S, X j) → ∀ j, X j := fun rest j =>
    if h : j = i then h.symm ▸ Classical.choice (inferInstance : Nonempty (X i))
    else rest ⟨j, by simp [S, h]⟩
  let choose : (∀ j : S, X j) → ℝ := fun rest => selectionIndicator (selected (restore rest))
  let charge : (∀ j : ({i} : Finset ι), X j) → ℝ := fun rest => cost (rest ⟨i, by simp⟩)
  have hrestore (draw : ∀ j, X j) : selected (restore (fun j : S => draw j)) ↔ selected draw := by
    apply hstable
    intro j hj
    dsimp only [restore]
    rw [dite_eq_right hj]
  have hind := (iIndepFun_pi (μ := μ) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)).indepFun_finset S {i} (by simp [S])
      (fun _ => measurable_pi_apply _)
  have hcomp := hind.comp (measurable_of_finite choose) (measurable_of_finite charge)
  convert hcomp using 1
  · ext draw
    exact congrArg selectionIndicator (propext (hrestore draw).symm)
  · rfl

theorem fresh_coordinate_expected_cost (i : ι) (selected : (∀ j, X j) → Prop)
    (hstable : ∀ left right : ∀ j, X j,
      (∀ j, j ≠ i → left j = right j) → (selected left ↔ selected right))
    (cost : X i → ℝ) :
    (∫ draw, (selectionIndicator (selected draw)) * cost (draw i) ∂Measure.pi μ) =
      (∫ draw, (selectionIndicator (selected draw)) ∂Measure.pi μ) *
        (∫ value, cost value ∂μ i) := by
  classical
  rw [(fresh_coordinate_independent μ i selected hstable cost).integral_fun_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable]
  rw [integral_comp_eval (measurable_of_finite cost).aestronglyMeasurable]

/-- Summing the first-request charges costs at most the expected selected
width budget times the common per-width cost. -/
theorem fresh_coordinates_expected_sum_le
    (selected : ι → (∀ j, X j) → Prop)
    (hstable : ∀ i left right,
      (∀ j, j ≠ i → left j = right j) → (selected i left ↔ selected i right))
    (cost : (i : ι) → X i → ℝ) (width : ι → ℝ) (overhead budget : ℝ)
    (hoverhead : 0 ≤ overhead)
    (hcost : ∀ i, (∫ value, cost i value ∂μ i) ≤ width i * overhead)
    (hbudget : ∀ draw, ∑ i, (selectionIndicator (selected i draw)) * width i ≤ budget) :
    (∫ draw, ∑ i, (selectionIndicator (selected i draw)) * cost i (draw i) ∂Measure.pi μ) ≤
      budget * overhead := by
  classical
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [fresh_coordinate_expected_cost μ _ _ (hstable _) (cost _)]
  calc
    _ ≤ ∑ i, (∫ draw, (selectionIndicator (selected i draw)) ∂Measure.pi μ) *
        (width i * overhead) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcost i) (integral_nonneg fun draw => by unfold selectionIndicator; split_ifs <;> norm_num)
    _ = (∫ draw, ∑ i, (selectionIndicator (selected i draw)) * width i ∂Measure.pi μ) * overhead := by
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite), sum_mul]
      apply sum_congr rfl
      intro i _
      rw [integral_mul_const]
      ring
    _ ≤ budget * overhead := by
      apply mul_le_mul_of_nonneg_right _ hoverhead
      exact (integral_mono (Integrable.of_finite) (integrable_const _) hbudget).trans_eq (by simp)

/-- Concrete specialization to a finite adaptive read program. A key is
charged once even if later continuation code requests it repeatedly. -/
theorem finiteQuery_fresh_expected_cost_le (query : FiniteQuery ι)
    (answer : (i : ι) → X i → ℚ) (cost : (i : ι) → X i → ℝ)
    (width : ι → ℝ) (overhead budget : ℝ) (hoverhead : 0 ≤ overhead)
    (hcost : ∀ i, (∫ value, cost i value ∂μ i) ≤ width i * overhead)
    (hbudget : ∀ draw : ∀ j, X j,
      ∑ i, (selectionIndicator (i ∈ query.keys (fun j => answer j (draw j)))) * width i ≤ budget) :
    (∫ draw, ∑ i,
      (selectionIndicator (i ∈ query.keys (fun j => answer j (draw j)))) * cost i (draw i)
        ∂Measure.pi μ) ≤ budget * overhead := by
  apply fresh_coordinates_expected_sum_le μ
    (fun i (draw : ∀ j, X j) => i ∈ query.keys (fun j => answer j (draw j)))
    _ cost width overhead budget hoverhead hcost hbudget
  intro i left right hagree
  exact FiniteQuery.mem_keys_iff_of_agree_off _ _ i
    (fun j hj => congrArg (answer j) (hagree j hj)) query

end IndependentCost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Expected active work in the concrete pruned coarse tree

The counter records the array units of the actual execution; pruning stops
all descendant visits. Constant child overhead is charged to its expanded
parent. The linear-sweep proof converts these units to rational operations;
bit/RAM charging is separate.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u



/- Array units actually incurred before pruning terminates a subtree. -/


theorem coarseWorkMultiplier_nonneg (factor : ℝ) (D : ℕ) (hfactor : 0 ≤ factor) :
    0 ≤ coarseWorkMultiplier factor D :=
  sum_nonneg (fun _ _ => pow_nonneg hfactor _)

theorem coarseWorkMultiplier_succ (factor : ℝ) (D : ℕ) :
    coarseWorkMultiplier factor (D + 1) = 1 + factor * coarseWorkMultiplier factor D := by
  simp only [coarseWorkMultiplier]
  rw [sum_range_succ']
  simp only [pow_zero, pow_succ', ← mul_sum]
  ring

theorem coarseWorkMultiplier_le (factor : ℝ) (D : ℕ) (hfactor : 1 ≤ factor) :
    coarseWorkMultiplier factor D ≤ (D + 1 : ℕ) * factor ^ D := by
  have hpoint : ∀ r ∈ range (D + 1), factor ^ r ≤ factor ^ D := by
    intro r hr
    exact pow_le_pow_right₀ hfactor (by obtain := mem_range.mp hr; omega)
  have hsum := sum_le_sum hpoint
  simpa only [coarseWorkMultiplier, sum_const, card_range, nsmul_eq_mul] using hsum

theorem uniformMean_mono_dup1 {ι : Type*} [Fintype ι] (first second : ι → ℝ)
    (hle : ∀ i, first i ≤ second i) : uniformMean first ≤ uniformMean second := by
  exact div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hle i)) (by positivity)

theorem uniformMean_const_mul {ι : Type*} [Fintype ι] (constant : ℝ) (value : ι → ℝ) :
    uniformMean (fun i => constant * value i) = constant * uniformMean value := by
  simp only [uniformMean, ← mul_sum]
  ring

/-- Exact expected inverse allowance under the literal integer threshold
law. This identity is independent of all estimated arrays and accuracy. -/
theorem coarse_inverse_allowance_mean (B : ℕ) [NeZero B] (Q lam allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    uniformMean (fun draw : Fin B =>
      1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) =
        coarseInverseAllowanceFactor B Q lam / allowance := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlr : (0 : ℝ) < lam := by exact_mod_cast hlam
  have har : (0 : ℝ) < allowance := by exact_mod_cast ha
  have hpoint (draw : Fin B) :
      1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) =
        ((B : ℝ) * Q / (lam * allowance)) * (1 / (draw.val + 1 : ℕ)) := by
    have hr : (0 : ℝ) < (draw.val + 1 : ℕ) := by positivity
    simp only [coarseChildThreshold, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]
    field_simp
  simp_rw [hpoint]
  rw [uniformMean_const_mul]
  simp only [uniformMean, Fintype.card_fin]
  rw [coarse_sum_labels B (fun r => (1 : ℝ) / r)]
  unfold coarseInverseAllowanceFactor
  field_simp

theorem coarseBranch_word_length {B D : ℕ} {α : Type u}
    (children : Fin B → CoarseSourceTree B α D) :
    (CoarseSourceTree.branch children).word.length = ∑ i, (children i).word.length := by
  simp only [CoarseSourceTree.word, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]

/-- The expected active work has the paper's inverse-allowance bound.
The inequality holds regardless of every coarse accuracy event. -/
theorem coarseExpectedArrayWork_bound {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    coarseExpectedArrayWork k Q lam tree allowance ≤
      (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / allowance *
        coarseWorkMultiplier (coarseInverseAllowanceFactor B Q lam) D := by
  have hfactor : 0 ≤ coarseInverseAllowanceFactor B Q lam := by
    unfold coarseInverseAllowanceFactor
    apply mul_nonneg
    · exact div_nonneg (by exact_mod_cast hQ.le) (by exact_mod_cast hlam.le)
    · exact sum_nonneg (fun _ _ => by positivity)
  have haReal : (0 : ℝ) < allowance := by exact_mod_cast ha
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseExpectedArrayWork]
    split_ifs with hprune
    · exact mul_nonneg (div_nonneg (by positivity) haReal.le)
        (coarseWorkMultiplier_nonneg _ 0 hfactor)
    · have hwidth : (allowance : ℝ) < (CoarseSourceTree.leaf (B := B) letter).word.length := by
        exact_mod_cast lt_of_not_ge hprune
      simp only [coarseWorkMultiplier, zero_add, sum_range_one, pow_zero, mul_one]
      apply (le_div_iff₀ haReal).2
      nlinarith [show (0 : ℝ) ≤ (B * (2 * k + 1) : ℕ) by positivity]
  | @branch D children ih =>
    simp only [coarseExpectedArrayWork]
    split_ifs with hprune
    · exact mul_nonneg (div_nonneg (by positivity) haReal.le)
        (coarseWorkMultiplier_nonneg _ (D + 1) hfactor)
    · let charge : ℝ := (B * (2 * k + 1) : ℕ)
      let factor := coarseInverseAllowanceFactor B Q lam
      let multiplier := coarseWorkMultiplier factor D
      have hmeanBound (i : Fin B) :
          uniformMean (fun draw : Fin B => coarseExpectedArrayWork k Q lam (children i)
              (lam * coarseChildThreshold B Q allowance draw)) ≤
            charge * (children i).word.length * multiplier * (factor / allowance) := by
        have hpoint (draw : Fin B) :
            coarseExpectedArrayWork k Q lam (children i)
                (lam * coarseChildThreshold B Q allowance draw) ≤
              (charge * (children i).word.length * multiplier) *
                (1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) := by
          have hchildAllowance := mul_pos hlam (coarseChildThreshold_pos draw hQ ha)
          have hbound := ih i _ hchildAllowance (by exact_mod_cast hchildAllowance)
          convert hbound using 1
          all_goals try with_reducible_and_instances rfl
          dsimp [charge, multiplier, factor]
          ring
        have hmean := uniformMean_mono_dup1 _ _ hpoint
        rw [uniformMean_const_mul, coarse_inverse_allowance_mean B Q lam allowance hQ hlam ha] at hmean
        exact hmean
      have hmeanSum := sum_le_sum (s := univ) (fun i _ => hmeanBound i)
      have hlength : (∑ i, ((children i).word.length : ℝ)) =
          (CoarseSourceTree.branch children).word.length := by
        exact_mod_cast (coarseBranch_word_length children).symm
      have hsum : (∑ i, charge * (children i).word.length * multiplier * (factor / allowance)) =
          charge * (CoarseSourceTree.branch children).word.length / allowance * (factor * multiplier) := by
        calc
          _ = (charge * multiplier * (factor / allowance)) * ∑ i, ((children i).word.length : ℝ) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [hlength]; ring
      rw [hsum] at hmeanSum
      have hwidth : (allowance : ℝ) < (CoarseSourceTree.branch children).word.length := by
        exact_mod_cast lt_of_not_ge hprune
      have hcharge : charge ≤ charge * (CoarseSourceTree.branch children).word.length / allowance := by
        apply (le_div_iff₀ haReal).2
        dsimp [charge]
        nlinarith [show (0 : ℝ) ≤ (B * (2 * k + 1) : ℕ) by positivity]
      have htotal := add_le_add hcharge hmeanSum
      rw [coarseWorkMultiplier_succ]
      dsimp [charge, multiplier, factor] at htotal ⊢
      nlinarith

theorem coarseActiveChildrenWork_eq_sum {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (work : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D)) :
    coarseActiveChildrenWork Q lam allowance work children =
      (children.map (fun data =>
        work data.1 data.2.2 (lam * coarseChildThreshold B Q allowance data.2.1))).sum := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [coarseActiveChildrenWork, List.map_cons, List.sum_cons, ih]

theorem coarseActiveChildrenWork_ofFn {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (work : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D) :
    coarseActiveChildrenWork Q lam allowance work
        (List.ofFn fun i => (children i, draws i, below i)) =
      ∑ i : Fin B, work (children i) (below i) (lam * coarseChildThreshold B Q allowance (draws i)) := by
  rw [coarseActiveChildrenWork_eq_sum]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- The finite expectation recurrence is exactly the expectation of the
actual pruning-stopped execution counter under the concrete recursive law. -/
theorem coarseActiveArrayWork_integral {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws allowance : ℝ)
      ∂coarseDrawMeasure B D) = coarseExpectedArrayWork k Q lam tree allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseActiveArrayWork, coarseExpectedArrayWork]
    split_ifs <;> simp
  | @branch D children ih =>
    by_cases hprune : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance
    · have hzero : (fun draws : CoarseThresholdDraws B (D + 1) =>
          (coarseActiveArrayWork k Q lam (.branch children) draws allowance : ℝ)) = fun _ => 0 := by
        funext draws
        obtain ⟨draws, below⟩ := draws
        simp only [coarseActiveArrayWork, hprune, ↓reduceIte, Nat.cast_zero]
      rw [hzero]
      simp only [integral_zero, coarseExpectedArrayWork, hprune, ↓reduceIte]
    · let μ := (PMF.uniformOfFintype (Fin B)).toMeasure
      let ν := coarseDrawMeasure B D
      change (∫ data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D),
        (coarseActiveArrayWork k Q lam (.branch children) data allowance : ℝ)
        ∂((Measure.pi fun _ : Fin B => μ).prod (Measure.pi fun _ : Fin B => ν))) = _
      have hpoint (data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :
          (coarseActiveArrayWork k Q lam (.branch children) data allowance : ℝ) =
            (B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
              (coarseActiveArrayWork k Q lam (children i) (data.2 i)
                (lam * coarseChildThreshold B Q allowance (data.1 i)) : ℝ) := by
        obtain ⟨draws, below⟩ := data
        simp only [coarseActiveArrayWork, hprune, ↓reduceIte,
          coarseActiveChildrenWork_ofFn, Nat.cast_add, Nat.cast_sum]
      simp_rw [hpoint]
      rw [integral_prod _ (.of_finite)]
      have hinner (draws : Fin B → Fin B) :
          (∫ below : Fin B → CoarseThresholdDraws B D,
            ((B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
              (coarseActiveArrayWork k Q lam (children i) (below i)
                (lam * coarseChildThreshold B Q allowance (draws i)) : ℝ))
            ∂Measure.pi (fun _ : Fin B => ν)) =
          (B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
            coarseExpectedArrayWork k Q lam (children i)
              (lam * coarseChildThreshold B Q allowance (draws i)) := by
        rw [integral_add (integrable_const _) (.of_finite), integral_const, probReal_univ, one_smul,
          integral_finsetSum]
        · congr 1
          apply sum_congr rfl
          intro i hi
          rw [integral_comp_eval (μ := fun _ : Fin B => ν) (i := i)
            (f := fun below => (coarseActiveArrayWork k Q lam (children i) below
              (lam * coarseChildThreshold B Q allowance (draws i)) : ℝ))
            (measurable_of_finite _).aestronglyMeasurable]
          exact ih i _
        · intro i hi
          exact .of_finite
      simp_rw [hinner]
      rw [integral_add (integrable_const _) (.of_finite), integral_const, probReal_univ, one_smul,
        integral_finsetSum]
      · simp only [coarseExpectedArrayWork, hprune, ↓reduceIte]
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
          (f := fun draw => coarseExpectedArrayWork k Q lam (children i)
            (lam * coarseChildThreshold B Q allowance draw))
          (measurable_of_finite _).aestronglyMeasurable, uniform_integral]
      · intro i hi
        exact .of_finite

/-- Expected active work, stated directly for the actual execution law,
without any conditioning on accuracy. -/
theorem coarseActiveArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws allowance : ℝ)
      ∂coarseDrawMeasure B D) ≤
        (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / allowance *
          coarseWorkMultiplier (coarseInverseAllowanceFactor B Q lam) D := by
  rw [coarseActiveArrayWork_integral]
  exact coarseExpectedArrayWork_bound k Q lam tree allowance hQ hlam ha

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Expected array work of the actual dyadic initial estimator

These are expectations of the concrete pruning-stopped counters. The
linear penalty sweeps and representation bounds separately convert the
array units into arithmetic and RAM work.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

theorem coarseInverseAllowanceFactor_nonneg (B : ℕ) (Q lam : ℚ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) : 0 ≤ coarseInverseAllowanceFactor B Q lam := by
  unfold coarseInverseAllowanceFactor
  exact mul_nonneg (div_nonneg (by exact_mod_cast hQ) (by exact_mod_cast hlam))
    (sum_nonneg (fun _ _ => by positivity))

theorem coarseWorkMultiplier_mono (first second : ℝ) (D : ℕ)
    (hfirst : 0 ≤ first) (hle : first ≤ second) :
    coarseWorkMultiplier first D ≤ coarseWorkMultiplier second D := by
  exact sum_le_sum (fun _ _ => pow_le_pow_left₀ hfirst hle _)

/-- Root allowance equals the actual guessed distance. It cancels the
array width `2k+1` in expectation, uniformly over every positive guess. -/
theorem coarseRootArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D)
    (hk : 0 < k) (hQ : 0 < Q) (hlam : 0 < lam)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws k : ℝ)
      ∂coarseDrawMeasure B D) ≤
      3 * B * tree.word.length * (D + 1 : ℕ) * factor ^ D := by
  have hcounter := coarseActiveArrayWork_expected_bound k Q lam tree k hQ hlam (by exact_mod_cast hk)
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoefficient : (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / k ≤
      3 * B * tree.word.length := by
    apply (div_le_iff₀ hkReal).2
    push_cast
    have hnonnegative : (0 : ℝ) ≤ (B : ℝ) * tree.word.length := by positivity
    nlinarith
  have hmultiplier := (coarseWorkMultiplier_mono _ factor D
    (coarseInverseAllowanceFactor_nonneg B Q lam hQ.le hlam.le) hinverse).trans
      (coarseWorkMultiplier_le factor D hfactor)
  apply hcounter.trans
  exact (mul_le_mul_of_nonneg_right hcoefficient
    (coarseWorkMultiplier_nonneg _ D (coarseInverseAllowanceFactor_nonneg B Q lam hQ.le hlam.le))).trans
    (by
      have hmul := mul_le_mul_of_nonneg_left hmultiplier
        (show (0 : ℝ) ≤ 3 * B * tree.word.length by positivity)
      simpa only [mul_assoc] using hmul)

/- The initial estimator's actual sum of active array units, with zero
array work in its two direct branches. -/


/-- The actual complete initial computation has the paper's expected
array-work shape, on every execution and without conditioning on accuracy. -/
theorem coarseInitialArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α) (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 < Q) (hlam : 0 < lam)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseInitialArrayWork B D Q lam x y draws : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
        (D + 1 : ℕ) * factor ^ D := by
  classical
  have hnonnegative : (0 : ℝ) ≤
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
        (D + 1 : ℕ) * factor ^ D := by positivity
  by_cases hlong : 2 * x.length < y.length
  · simpa only [coarseInitialArrayWork, hlong, ↓reduceIte, Nat.cast_zero, integral_zero] using hnonnegative
  by_cases hxy : x = y
  · have hzero (draws) : coarseInitialArrayWork B D Q lam x y draws = 0 := by
      unfold coarseInitialArrayWork
      rw [ite_eq_right hlong, ite_eq_left hxy]
    simp_rw [hzero, Nat.cast_zero, integral_zero]
    exact hnonnegative
  simp only [coarseInitialArrayWork, hlong, hxy, ↓reduceIte, Nat.cast_sum]
  rw [integral_finsetSum univ (by intro i hi; exact .of_finite)]
  have hpoint (i : CoarseGuessIndex (coarseEntryWidth x y)) :
      (∫ draws, (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) Q lam
        (coarseEntryTree B D x y) (draws i) (coarseGuess (coarseEntryWidth x y) i) : ℝ)
        ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      3 * B * coarseEntryWidth x y * (D + 1 : ℕ) * factor ^ D := by
    unfold coarseInitialMeasure
    rw [integral_comp_eval (μ := fun _ : CoarseGuessIndex (coarseEntryWidth x y) => coarseDrawMeasure B D)
      (i := i) (f := fun draws => (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) Q lam
        (coarseEntryTree B D x y) draws (coarseGuess (coarseEntryWidth x y) i) : ℝ))
      (measurable_of_finite _).aestronglyMeasurable]
    have hbound := coarseRootArrayWork_expected_bound (coarseGuess (coarseEntryWidth x y) i)
      Q lam (coarseEntryTree B D x y) (by dsimp [coarseGuess] <;> positivity) hQ hlam factor hfactor hinverse
    rw [coarseEntryTree_word B D x y hcapacity,
      coarsePadTo_length _ _ (le_max_left _ _)] at hbound
    exact hbound
  have hsum := sum_le_sum (s := univ) (fun i _ => hpoint i)
  apply hsum.trans_eq
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWidthWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The direct long-target branch removes dependence of initial-entry
work on the target interval width. This is the source-width charge used
when coarse leaves are summed over the physical dependency tree. -/

namespace EditApproximation

open MeasureTheory

theorem coarseInitialArrayWork_expected_source_width {α : Type*} [DecidableEq α]
    {B D : ℕ} [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α) (N : ℕ)
    (hsize : coarseEntryWidth x y ≤ N) (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 < Q) (hlam : 0 < lam) (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseInitialArrayWork B D Q lam x y draws : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
    6 * B * x.length * (Nat.clog 2 N + 1 : ℕ) * (D + 1 : ℕ) * factor ^ D := by
  have hnonneg : 0 ≤ factor := le_trans (by norm_num) hfactor
  by_cases hlong : 2 * x.length < y.length
  · have hzero (draws) : coarseInitialArrayWork B D Q lam x y draws = 0 := by
      simp only [coarseInitialArrayWork, ite_eq_left hlong]
    simp only [hzero, Nat.cast_zero, integral_zero]
    positivity
  · have hwidth : coarseEntryWidth x y ≤ 2 * x.length := by
      unfold coarseEntryWidth
      omega
    have hlog := Nat.clog_mono_right 2 hsize
    have h := coarseInitialArrayWork_expected_bound Q lam x y hcapacity hQ hlam factor hfactor hinverse
    apply h.trans
    calc
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
          (D + 1 : ℕ) * factor ^ D ≤
        3 * B * (2 * (x.length : ℝ)) * (Nat.clog 2 N + 1 : ℕ) * (D + 1 : ℕ) * factor ^ D := by
          gcongr
          · exact_mod_cast hwidth
      _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWorkAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The depth-dependent scalar overhead of the actual initial estimator.
The expected array-counter bound includes every pruning outcome. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computedCoarseDepth_le_max (N n : ℕ) (hn : n ≤ N) :
    computedCoarseDepth N n ≤ computedMaxCoarseDepth N := by
  change Nat.clog (integerParameters N).B (max 1 n) ≤ Nat.clog (integerParameters N).B (max 1 N)
  exact Nat.clog_mono_right (integerParameters N).B (max_le_max le_rfl hn)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseWidthCost
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coarse array counter has a common source-width overhead.
Its exponent is sublinear in the computed logarithmic height. -/

namespace EditApproximation

open MeasureTheory

theorem coarse_array_bound_mono (B n L factor : ℝ) (D E : ℕ)
    (hB : 0 ≤ B) (hn : 0 ≤ n) (hL : 0 ≤ L) (hfactor : 1 ≤ factor) (hD : D ≤ E) :
    6 * B * n * L * (D + 1 : ℕ) * factor ^ D ≤
      n * (6 * B * L * (E + 1 : ℕ) * factor ^ E) := by
  have hcount : ((D + 1 : ℕ) : ℝ) ≤ (E + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hD 1
  have hpower := pow_le_pow_right₀ hfactor hD
  calc
    _ ≤ 6 * B * n * L * (E + 1 : ℕ) * factor ^ E := by
      apply mul_le_mul _ hpower (pow_nonneg (by linarith) _) (by positivity)
      exact mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- The common overhead dominates the actual expected coarse array work
at every source/target interval, including the direct long-target branch. -/
theorem computed_coarse_expected_source_width {α : Type*} [DecidableEq α]
    (N B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (hB : B = (integerParameters N).B) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (x y : List α) (D : ℕ) (hDcomputed : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hsize : coarseEntryWidth x y ≤ N) :
    (∫ draw, (coarseInitialArrayWork B D
      (initialThresholdQ N) (initialLambda N) x y draw : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      (x.length : ℝ) * computedCoarseWidthOverhead N := by
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hD : D ≤ computedMaxCoarseDepth N :=
    hDcomputed.trans_le (computedCoarseDepth_le_max N (coarseEntryWidth x y) hsize)
  have hcapacity : coarseEntryWidth x y ≤ B ^ D := by
    rw [hB, hDcomputed]
    exact (computed_coarse_depth N _ hN hsize hell).1
  have hHQ : (0 : ℚ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hHR : (1 : ℝ) ≤ inputHeight N := by exact_mod_cast hH
  have hQ : 0 < initialThresholdQ N := pow_pos hHQ 4
  have hlam : 0 < initialLambda N := div_pos (by norm_num) (mul_pos (by norm_num) hHQ)
  have hc := coarseInitialArrayWork_expected_source_width (B := B) (D := D)
    (initialThresholdQ N) (initialLambda N) x y N hsize hcapacity
    hQ hlam ((inputHeight N : ℝ) ^ 8) (one_le_pow₀ hHR) hinverse
  apply hc.trans
  have hm := coarse_array_bound_mono (B : ℝ) (x.length : ℝ) (Nat.clog 2 N + 1 : ℕ)
    ((inputHeight N : ℝ) ^ 8) D (computedMaxCoarseDepth N)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (one_le_pow₀ hHR) hD
  apply hm.trans_eq
  simp only [computedCoarseWidthOverhead, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, hB, ← pow_mul]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseFirstRequestCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-request work for a complete independent coarse source. The
query is adaptive; each entry is charged only on its first appearance.
No conditioning on seed correctness occurs in this estimate. -/

namespace EditApproximation

open MeasureTheory

section FirstRequest

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
  (N B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : ι → ℕ) (x y : ι → List α) (query : FiniteQuery ι)

theorem coarseFirstRequestWork_expected_le
    (hB : B = (integerParameters N).B) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hdepth : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hsize : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (budget : ℝ)
    (hbudget : ∀ draw : CoarseFullSeedDraws B depth x y,
      ((query.cost (fun i => (coarseFullSeedTable N B depth x y draw i : ℚ))
        (fun i => (x i).length) : ℕ) : ℝ) ≤ budget) :
    (∫ draw, coarseFirstRequestWork N B depth x y query draw
      ∂coarseFullSeedMeasure B depth x y) ≤ budget * computedCoarseWidthOverhead N := by
  let μ := fun i => coarseInitialMeasure B (depth i) (coarseEntryWidth (x i) (y i))
  let answer := fun i draw =>
    (coarseInitialValue B (depth i) (initialThresholdQ N) (initialLambda N) N (x i) (y i) draw : ℚ)
  let cost := fun i draw =>
    (coarseInitialArrayWork B (depth i) (initialThresholdQ N) (initialLambda N) (x i) (y i) draw : ℝ)
  have hcost (i) : (∫ value, cost i value ∂μ i) ≤
      ((x i).length : ℝ) * computedCoarseWidthOverhead N :=
    computed_coarse_expected_source_width N B hB hN hell hinverse (x i) (y i)
      (depth i) (hdepth i) (hsize i)
  have hselected (draw : CoarseFullSeedDraws B depth x y) :
      (∑ i, selectionIndicator (i ∈ query.keys (fun j => answer j (draw j))) *
        ((x i).length : ℝ)) ≤ budget := by
    have hs := sum_selected_nat_weights_le (query.keys (fun j => answer j (draw j)))
      (fun i => (x i).length)
    have hb := hbudget draw
    rw [FiniteQuery.cost_eq_sum] at hb
    exact hs.trans hb
  have h := finiteQuery_fresh_expected_cost_le μ query answer cost
    (fun i => ((x i).length : ℝ)) (computedCoarseWidthOverhead N) budget
    (Nat.cast_nonneg _) hcost hselected
  exact h

end FirstRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

namespace DependencyExpansion

section Builder

variable {ι : Type*} (d r m n : ι → ℕ)
  (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
  (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
  (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x)

theorem build_depth (root : ι) : (build d r m n s e hs he root).depth = d root := by
  rw [build]
  rfl

end Builder

end DependencyExpansion
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedCoarseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All initial-entry information used by a charged table body arrives
through explicit requests. Flattening those requests gives an adaptive
coarse oracle program whose shape is independent of coarse answers. -/

namespace EditApproximation

namespace FiniteQuery

theorem substitute_cost {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (weight : κ → ℕ) (query : FiniteQuery ι) :
    (query.substitute ask).cost oracle weight = query.cost
      (fun key => (ask key).value oracle) (fun key => (ask key).cost oracle weight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, cost_bind, cost]
    exact congrArg ((ask key).cost oracle weight + ·) (ih ((ask key).value oracle))

theorem substitute_value {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).value oracle = query.value (fun key => (ask key).value oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, bind_value, value]
    exact ih ((ask key).value oracle)

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Random source coordinates and recursive table entries share the same
memo evaluator. Source coordinates have rank zero; each table rank is
shifted by one. Consequently repeated source reads reuse their stored draw. -/

namespace EditApproximation

namespace SourceRanked

variable {σ κ : Type*}







 theorem body_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    (body tableRank tableBody sourceValue key).value
      (fun next => value sourceValue tableValue next.val) = value sourceValue tableValue key := by
  cases key with
  | inl source => rfl
  | inr table =>
    rw [body, FiniteQuery.mapKeys_value]
    have horacle : (fun next => value sourceValue tableValue next.val) ∘ child tableRank table =
        Sum.elim sourceValue (fun next => tableValue next.val) := by
      funext next
      cases next <;> rfl
    rw [horacle]
    exact hbody table

 theorem program_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    rankedProgramValue (rank tableRank) (body tableRank tableBody sourceValue) key =
      value sourceValue tableValue key :=
  rankedProgramValue_eq _ _ _ (body_value tableRank tableBody sourceValue tableValue hbody) key

end SourceRanked

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryCostOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.FiniteQuery

theorem cost_mono_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (hle : ∀ key, left key ≤ right key) :
    program.cost oracle left ≤ program.cost oracle right := by
  induction program with
  | done result => exact le_rfl
  | read key next ih => exact Nat.add_le_add (hle key) (ih (oracle key))

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source leaves add only their executed read count to each table body.
Projecting them away preserves the table dependency program, so a uniform
local source budget multiplies its uncached request bound. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

include hbody in
 theorem projectedProgram_value (key : κ) :
    rankedProgramValue tableRank (projectedBody tableRank tableBody sourceValue) key = tableValue key :=
  rankedProgramValue_eq tableRank _ tableValue
    (projectedBody_value tableRank tableBody sourceValue tableValue hbody) key

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseOracle
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed accepted source family leaves a nonanticipating coarse query:
coarse values enter only when the corresponding leaf is requested. -/

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

theorem physicalRandomGlobalQuery_refinement_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : PhysicalTableRequest M J target.length)
    (hi : ¬ parent.index ≤ T) (hd : parent.node.1.val < J)
    (hw : ¬ (physicalSourceInterval source.length parent.node).hi -
      (physicalSourceInterval source.length parent.node).lo ≤ 1) :
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger left parent =
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger right parent := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨by omega, hd, hw⟩, dite_eq_left ⟨by omega, hd, hw⟩]

/-- Coarse answers enter the charged program only at coarse leaves. -/
theorem chargedRandomGlobalQuery_table_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger left (.inr parent) =
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger right (.inr parent) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  split_ifs with hi hd hw
  · rfl
  · rfl
  · unfold physicalRandomBoundedQuery SourceRanked.restrictBody
    rw [physicalRandomGlobalQuery_refinement_initial_independent source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger left right parent.val hi hd hw]
  · rfl

theorem chargedRandomCoarseQuery_value
    (initial : PhysicalEntry M J target.length → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
    rankedProgramValue ChargedPhysicalRequest.rank
      (SourceRanked.projectedBody ChargedPhysicalRequest.rank
        (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
  have hall : ∀ level root, root.rank = level →
      (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
      rankedProgramValue ChargedPhysicalRequest.rank
        (SourceRanked.projectedBody ChargedPhysicalRequest.rank
          (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedProgramValue]
        rfl
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_value, rankedProgramValue]
        unfold SourceRanked.projectedBody
        rw [
          chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S passes copies
            factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        congr 1
        funext child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKeys
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryMemo.mapValues_insert _root_.OAI.EditApproximation.BinaryMemo.mapValues_left _root_.OAI.EditApproximation.BinaryMemo.mapValues_lookup _root_.OAI.EditApproximation.BinaryMemo.mapValues_nodes _root_.OAI.EditApproximation.BinaryMemo.mapValues_right _root_.OAI.EditApproximation.BinaryMemo.mapValues_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cache miss is among the requests of the uncached execution with
identical answers. This includes adaptive continuations and cache hits. -/

namespace EditApproximation

namespace FiniteQuery

theorem substitute_keys {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).keys oracle =
      (query.keys (fun key => (ask key).value oracle)).flatMap (fun key => (ask key).keys oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, keys_bind, keys, List.flatMap_cons]
    rw [ih]

theorem run_freshKeys_mem {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ) (allowed : ι → List κ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
      memoSound bits encode expected (ask key memory).memory ∧
      ∀ item ∈ (ask key memory).freshKeys, item ∈ allowed key)
    (query : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    ∀ item ∈ (run ask query memory).freshKeys, item ∈ (query.keys answer).flatMap allowed := by
  induction query generalizing memory with
  | done value => simp only [run, List.not_mem_nil, false_implies, implies_true]
  | read key next ih =>
    have hf := hask key memory hsound
    intro item hitem
    simp only [run, List.mem_append] at hitem
    rcases hitem with hfirst | hrest
    · exact List.mem_flatMap.mpr ⟨key, List.mem_cons_self, hf.2.2 item hfirst⟩
    · have hr := ih (ask key memory).value (ask key memory).memory hf.2.1 item hrest
      rw [hf.1] at hr
      obtain ⟨child, hc, hi⟩ := List.mem_flatMap.mp hr
      exact List.mem_flatMap.mpr ⟨child, List.mem_cons_of_mem key hc, hi⟩

theorem eraseSources_inr_mem_iff {σ κ : Type*} (source : σ → ℚ) (table : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) (key : κ) :
    Sum.inr key ∈ query.keys (Sum.elim source table) ↔
      key ∈ (eraseSources source query).keys table := by
  induction query with
  | done value => simp only [keys, eraseSources, List.not_mem_nil]
  | read next continuation ih =>
    cases next with
    | inl scalar => simpa only [keys, eraseSources, Sum.elim_inl, List.mem_cons,
        Sum.inr_ne_inl, false_or] using ih (source scalar)
    | inr child => simpa only [keys, eraseSources, Sum.elim_inr, List.mem_cons,
        Sum.inr.injEq] using or_congr Iff.rfl (ih (table child))

end FiniteQuery

theorem rankedMemoEvaluate_freshKeys_mem {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
      item ∈ rankedUncachedKeys rank program key := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
        item ∈ rankedUncachedKeys rank program key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · simp
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
            ∀ item ∈ (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys,
              item ∈ rankedUncachedKeys rank program child.val := by
          intro child previous hp
          have hs := rankedMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp⟩
        have hr := FiniteQuery.run_freshKeys_mem bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child => rankedUncachedKeys rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        intro item hi
        simp only [List.mem_cons] at hi
        rw [rankedUncachedKeys]
        rcases hi with rfl | hi
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem key (hr item hi)
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

include hbody

/-- Forgetting source leaves preserves every table request, including
those which the mixed memo execution first encounters after a cache hit. -/
theorem uncachedKeys_table_mem (root item : κ)
    (hitem : Sum.inr item ∈ rankedUncachedKeys (rank tableRank)
      (body tableRank tableBody sourceValue) (.inr root)) :
    item ∈ rankedUncachedKeys tableRank (projectedBody tableRank tableBody sourceValue) root := by
  let mixed := body tableRank tableBody sourceValue
  let projected := projectedBody tableRank tableBody sourceValue
  have hvm (key : Sum σ κ) : rankedProgramValue (rank tableRank) mixed key =
      value sourceValue tableValue key := program_value tableRank tableBody sourceValue tableValue hbody key
  have hvp (key : κ) : rankedProgramValue tableRank projected key = tableValue key :=
    projectedProgram_value tableRank tableBody sourceValue tableValue hbody key
  have hall : ∀ level root, tableRank root = level → ∀ item,
      Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inr root) →
      item ∈ rankedUncachedKeys tableRank projected root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel item hm
      rw [rankedUncachedKeys] at hm ⊢
      rcases List.mem_cons.mp hm with heq | hm
      · exact List.mem_cons.mpr (.inl (Sum.inr.inj heq))
      · have hanswer :
            (fun next => rankedProgramValue (rank tableRank) mixed next.val) ∘ child tableRank root =
              Sum.elim sourceValue (fun next => tableValue next.val) := by
          funext next
          rw [Function.comp_apply, hvm]
          cases next <;> rfl
        change Sum.inr item ∈ ((mixed (.inr root)).keys _).flatMap _ at hm
        dsimp only [mixed, body] at hm
        rw [FiniteQuery.mapKeys_keys, hanswer] at hm
        obtain ⟨next, hn, hi⟩ := List.mem_flatMap.mp hm
        obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hn
        cases raw with
        | inl scalar =>
          change Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inl scalar) at hi
          rw [rankedUncachedKeys] at hi
          simp only [mixed, body, FiniteQuery.keys, List.flatMap_nil,
            List.mem_cons, Sum.inr_ne_inl, List.not_mem_nil, or_false] at hi
        | inr next =>
          have ht := (FiniteQuery.eraseSources_inr_mem_iff sourceValue
            (fun child => tableValue child.val) (tableBody root) next).mp hr
          have hi' := ih (tableRank next.val) (hlevel ▸ next.property) next.val rfl item hi
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨next, ?_, hi'⟩
          change next ∈ (FiniteQuery.eraseSources sourceValue (tableBody root)).keys
            (fun child => rankedProgramValue tableRank projected child.val)
          simpa only [hvp] using ht
  exact hall (tableRank root) root rfl item hitem

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Keys

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (initial : PhysicalEntry M J target.length → ℕ)

local notation "mixed" => chargedRandomGlobalQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixed sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer

 theorem chargedRandomCoarseQuery_uncached_keys
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  have hall : ∀ level root, root.rank = level → ∀ entry,
      Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root →
      entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel entry he
      cases root with
      | inl base =>
        rw [rankedUncachedKeys] at he
        simp only [SourceRanked.projectedBody, chargedRandomGlobalQuery,
          FiniteQuery.eraseSources, FiniteQuery.keys, List.flatMap_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inl.injEq] at he
        subst entry
        rw [chargedRandomCoarseQuery]
        exact List.mem_cons_self
      | inr parent =>
        rw [rankedUncachedKeys] at he
        rcases List.mem_cons.mp he with he | he
        · cases he
        obtain ⟨child, hc, he⟩ := List.mem_flatMap.mp he
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_keys]
        apply List.mem_flatMap.mpr
        refine ⟨child, ?_, ih child.val.rank (hlevel ▸ child.property) child.val rfl entry he⟩
        have hv (child) := chargedRandomCoarseQuery_value source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        exact hc
  exact hall root.rank root rfl entry hentry

 theorem chargedRandomMemo_coarse_key
    (values : ChargedPhysicalRequest M J target.length passes copies T S → ℚ)
    (hbody : ∀ key, (mixed key).value (Sum.elim sourceAnswer (fun next => values next.val)) = values key)
    (bits : ℕ) (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).freshKeys) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  apply chargedRandomCoarseQuery_uncached_keys source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial root entry
  apply SourceRanked.uncachedKeys_table_mem ChargedPhysicalRequest.rank mixed sourceAnswer values hbody root
    (Sum.inl entry)
  exact rankedMemoEvaluate_freshKeys_mem _ _ bits encode hinjective hbounded (.inr root) .empty
    (memoSound_empty _ _ _) (.inr (.inl entry)) hentry

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

theorem queryRequestList_cost (key : κ) (weight : κ → ℕ) :
    (program key).cost
        (fun child => rankedProgramValue (fun x => depth x + index x) program child.val)
        (fun child => weight child.val) =
      ((queryRequestList depth index program key).map weight).sum := by
  rw [FiniteQuery.cost_eq_sum]
  simp only [queryRequestList, List.map_map, Function.comp_def]

theorem sum_map_partition (predicate : κ → Bool) (weight : κ → ℕ) (keys : List κ) :
    ((keys.filter (fun key => !predicate key)).map weight).sum +
      ((keys.filter predicate).map weight).sum = (keys.map weight).sum := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    cases hp : predicate key <;> simp only [List.filter_cons, hp, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, reduceIte, List.map_cons, List.sum_cons]
    all_goals omega

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

theorem queryDependencyExpansion_depth (root : κ) :
    (queryDependencyExpansion depth index program progress root).depth = depth root :=
  DependencyExpansion.build_depth _ _ _ _ _ _ _ _ root

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWeightedWork
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Per-request local work summed along the actual adaptive expansion.
This is a weighted analogue of the uncached request count. -/

namespace EditApproximation

open Finset

section Weighted

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})
  (progress : ∀ key child, child ∈ queryRequestList depth index program key →
    (depth child < depth key ∧ index child ≤ index key) ∨
    (depth child ≤ depth key ∧ index child < index key))

theorem queryDependencyExpansion_weighted (weight : ℕ → ℕ) (root : κ) :
    (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
      rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
  have hall : ∀ level root, depth root + index root = level →
      (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
        rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hroot
      conv_lhs => unfold queryDependencyExpansion
      rw [DependencyExpansion.build]
      change weight (depth root) + (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) +
        (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) = _
      have hs (i : Fin (querySameRequests depth index program root).length) :=
        querySameRequests_progress depth index program progress root i
      have he (i : Fin (queryEarlierRequests depth index program root).length) :=
        queryEarlierRequests_progress depth index program progress root i
      have hsame : (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) =
        (((querySameRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (querySameRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((querySameRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_lt_of_le (hs i).1 (hs i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      have hearlier : (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) =
        (((queryEarlierRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (queryEarlierRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((queryEarlierRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_le_of_lt (he i).1 (he i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      rw [hsame, hearlier, rankedUncachedWork, queryRequestList_cost]
      have hp := sum_map_partition (fun child => decide (index child < index root))
        (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))
        (queryRequestList depth index program root)
      change weight (depth root) + _ + _ = _ + weight (depth root)
      change _ + _ = _ at hp
      dsimp only [querySameRequests, queryEarlierRequests]
      omega
  exact hall (depth root + index root) root rfl

end Weighted

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial) sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger sourceAnswer
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

 theorem chargedRandomCoarseQuery_cost_le (weight : ℕ → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => weight (J - entry.1.1.val)) ≤
    rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
  have hall : ∀ level root, root.rank = level →
      (coarse root).cost (fun entry => (initial entry : ℚ))
        (fun entry => weight (J - entry.1.1.val)) ≤
      rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedUncachedWork]
        simp only [FiniteQuery.cost, SourceRanked.projectedBody, chargedRandomGlobalQuery, FiniteQuery.eraseSources, ChargedPhysicalRequest.depth, Nat.zero_add,
          Nat.add_zero, le_refl]
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_cost]
        have hv (child) := chargedRandomCoarseQuery_value source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        rw [rankedUncachedWork]
        apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans (Nat.le_add_right _ _)
        intro child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

variable
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody
 theorem chargedRandomCoarseQuery_width_cost_le
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => 1 + source.length ⌈/⌉ M ^ entry.1.1.val) ≤
    (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length := by
  have hweight := chargedRandomCoarseQuery_cost_le source target N P H T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial
    (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  have hdepth : ∀ entry : PhysicalEntry M J target.length,
      J - (J - entry.1.1.val) = entry.1.1.val := by
    intro entry
    have := entry.1.1.isLt
    omega
  simp only [hdepth] at hweight
  apply hweight.trans_eq
  have hw := queryDependencyExpansion_weighted depth index program
    (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  change _ = (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depthWeightedCount
      (fun d => 1 + source.length ⌈/⌉ M ^ (_ - d))
  rw [show (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depth = depth root from
    queryDependencyExpansion_depth depth index program
      (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root]
  rw [hroot]
  exact hw.symm

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

 theorem physicalFamilyCoarseQuery_cost_le_width
    (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (hroot : root.depth = J) :
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root).cost (fun entry => (initial entry : ℚ))
      (fun entry => (physicalSource source entry.1).length) ≤
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length := by
  apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans
    (chargedRandomCoarseQuery_width_cost_le source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta readGroup readInteger answer initial group
      (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw) root hroot)
  intro entry
  rw [physicalSource_length_eq]
  exact (sourceIntervalAt_width M source.length entry.1.1.val (Nat.pos_of_neZero M) entry.1.2).trans
    (Nat.le_add_left _ 1)

variable (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

 theorem physicalFamilyCoarseWork_expected_le
    (hP : 0 < P) (hN : 0 < N) (hell : 200 ≤ ell)
    (hB : B = (integerParameters N).B) (hsize : source.length + target.length ≤ N)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S)
    (hroot : root.depth = J) (budget : ℝ)
    (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
      ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        hP draw root).widthWork M source.length : ℝ) ≤ budget) :
    (∫ coarse, physicalFamilyCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth root coarse
      ∂coarseFullSeedMeasure B depth
        (fun entry => physicalSource source entry.1)
        (fun entry => substring target entry.2.lo entry.2.hi)) ≤
    budget * computedCoarseWidthOverhead N := by
  have hentries (entry : PhysicalEntry M J target.length) :
      coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) ≤ N := by
    apply max_le
    · exact (physicalSource_length_le source entry.1).trans (by omega)
    · have hl : (substring target entry.2.lo entry.2.hi).length ≤ target.length := by
        simp only [substring, List.length_drop, List.length_take]
        exact (Nat.sub_le _ _).trans (min_le_right _ _)
      exact hl.trans (by omega)
  apply coarseFirstRequestWork_expected_le N B depth _ _ _ hB hN hell hdepth hentries hinverse budget
  intro coarse
  have hc := physicalFamilyCoarseQuery_cost_le_width source target N P H T S passes copies
    factor multiplier tau eta kappa delta draw
    (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)) hP root hroot
  exact ((Nat.cast_le (α := ℝ)).mpr hc).trans (hwidth coarse)

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyMemoCoarse
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory

private theorem selectionIndicator_le {p q : Prop} (h : p → q) :
    selectionIndicator p ≤ selectionIndicator q := by
  classical
  by_cases hp : p
  · have hq := h hp
    simp only [selectionIndicator, hp, hq, ite_true, if_true, le_refl]
  · simp only [selectionIndicator, hp, ite_false, if_false]
    split <;> norm_num

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)
  (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw



omit [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] in
 theorem physicalFamilyMemoCoarseWork_le (hP : 0 < P) (bits : ℕ) (encode : Sum Key Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) :
    physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth bits encode root coarse ≤
    physicalFamilyCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth root coarse := by
  classical
  let initial := clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse)
  have hkey (entry : PhysicalEntry M J target.length) :=
    chargedRandomMemo_coarse_key source target N P ell exponent H (ell ^ 80) T S
      (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyRequestValue source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      bits encode hinjective hbounded root entry
  unfold physicalFamilyMemoCoarseWork physicalFamilyCoarseWork coarseFirstRequestWork
  apply Finset.sum_le_sum
  intro entry _
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact selectionIndicator_le (hkey entry)


 theorem physicalFamilyMemoCoarseWork_expected_le_oai (hP : 0 < P) (hN : 0 < N)
    (hell : 200 ≤ ell) (hB : B = (integerParameters N).B)
    (hsize : source.length + target.length ≤ N)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (bits : ℕ) (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (root : Table) (hroot : root.depth = J)
    (budget : ℝ)
    (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
      ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        hP draw root).widthWork M source.length : ℝ) ≤ budget) :
    (∫ coarse, physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth bits encode root coarse
      ∂coarseFullSeedMeasure B depth
        (fun entry => physicalSource source entry.1)
        (fun entry => substring target entry.2.lo entry.2.hi)) ≤
    budget * computedCoarseWidthOverhead N := by
  classical
  apply (integral_mono Integrable.of_finite Integrable.of_finite (fun coarse =>
    physicalFamilyMemoCoarseWork_le source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth hP bits encode hinjective hbounded root coarse)).trans
  exact physicalFamilyCoarseWork_expected_le source target N P H T S passes copies factor multiplier
    tau eta kappa delta draw B depth hP hN hell hB hsize hdepth hinverse root hroot budget hwidth

end Coarse

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le_oai.{u_1} := @OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le_oai.{u_1}
