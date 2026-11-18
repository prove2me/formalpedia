-- Prove2me | solution 1 for OAI.EditApproximation.queryRefinementGather_refines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:41.289208+00:00
-- url     : https://prove2.me/submissions/13672f7b-339d-4d3b-b4f6-24818a15016b

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_querySharedCellInputsWithWork_value

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Callback work is retained when a finite loop is supplied with a
costed reader. These lemmas compare the literal loop counters, so a
lookup cannot disappear when its returned word is passed to arithmetic. -/

namespace EditApproximation

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem arithmeticFlatMapWithWork_factor {α β : Type*} (read plain : α → List β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤ (arithmeticFlatMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv]
      have hl : (plain x).1.length ≤ (plain x).1.length * K := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (plain x).1.length hK
      nlinarith only [hc, ht.2, hl, hK]

theorem filterWithWork_length_le_cost {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    xs.length ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, filterWithWork]; omega

theorem filterWithWork_add_read {α : Type*} (test : α → Bool × ℕ)
    (readCost : α → ℕ) (xs : List α) (R : ℕ) (hR : ∀ x ∈ xs, readCost x ≤ R) :
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).1 =
      (filterWithWork test xs).1 ∧
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).2 ≤
      (filterWithWork test xs).2 * (R + 1) := by
  have h := filterWithWork_extra (fun x => ((test x).1, (test x).2 + readCost x))
    test readCost xs (fun _ _ => rfl) (fun _ _ => le_rfl)
  have hs := sum_map_le_length_mul xs readCost R hR
  have hl := filterWithWork_length_le_cost test xs
  refine ⟨h.1, ?_⟩
  nlinarith only [h.2, hs, hl]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCellReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reader-aware whole-cell construction. Every eligibility test reads its
initial word, and every accepted band and selected action uses the counted
reader kernels. -/

namespace EditApproximation

namespace BinaryFraction



theorem cellCentersReadWithWork_eq_cost {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (cell : ℕ × ℕ)
    (R : ℕ) (hr : ∀ r, (initial r).2 ≤ R) :
    (cellCentersReadWithWork P F b a theta initial cell).1 =
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).1 ∧
    (cellCentersReadWithWork P F b a theta initial cell).2 ≤
      (cellCentersWithWork P F b a theta (fun r => (initial r).1) cell).2 * (R + 1) := by
  have hs := filterWithWork_add_read
    (fun r => centerEligibilityWithWork b F a (initial r).1) (fun r => (initial r).2)
    (cellStatesWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
      (canonicalMulWithWork theta (nat b)).1 cell).1 R (fun r _ => hr r)
  unfold cellCentersReadWithWork cellCentersWithWork
  dsimp only
  have he : (fun r => let word := initial r; let tested := centerEligibilityWithWork b F a word.1;
      (tested.1, word.2 + tested.2)) =
      (fun r => ((centerEligibilityWithWork b F a (initial r).1).1,
        (centerEligibilityWithWork b F a (initial r).1).2 + (initial r).2)) := by
    funext r
    simp only [Nat.add_comm]
  rw [he, hs.1]
  exact ⟨rfl, by nlinarith only [hs.2]⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Query-local representative construction reads its finite initial
table explicitly. Each center lookup is charged before testing it. -/

namespace EditApproximation
namespace BinaryFraction



theorem representativeScaleReadWithWork_eq_cost {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (radius : List Bool)
    (query : TargetInterval n) (e R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (representativeScaleReadWithWork P F a read radius query e).1 =
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).1 ∧
    (representativeScaleReadWithWork P F a read radius query e).2 ≤
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius) query.lo query.hi
  have h := filterWithWork_add_read (fun r => centerEligibilityWithWork (2 ^ e) F a (read r).1)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simp only [representativeScaleReadWithWork, representativeScalePlainWithWork, spacing, points, h.1]
  · unfold representativeScaleReadWithWork representativeScalePlainWithWork
    change spacing.2 + points.2 + _ + _ + e + 5 ≤ (spacing.2 + points.2 + _ + _ + e + 5) * _
    rw [h.1]
    nlinarith only [h.2]



theorem localRepresentativeReadWithWork_eq_cost {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (query : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (localRepresentativeReadWithWork N P F a read query).1 =
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).1 ∧
    (localRepresentativeReadWithWork N P F a read query).2 ≤
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).2 * (R + 2) := by
  let scales := queryExponentsWithWork N F a (read query).1
  let radius := naturalCeilingWithWork (read query).1
  let plain := representativeScalePlainWithWork P F a (fun r => (read r).1) radius.1 query
  let withRead := representativeScaleReadWithWork P F a read radius.1 query
  have h := arithmeticFlatMapWithWork_factor withRead plain scales.1 (R + 1) (by omega)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).1)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).2)
  have hquery := hR query
  constructor
  · exact h.1
  · change (read query).2 + scales.2 + radius.2 +
      (arithmeticFlatMapWithWork withRead scales.1).2 + 3 ≤
      (scales.2 + radius.2 + (arithmeticFlatMapWithWork plain scales.1).2 + 3) * (R + 2)
    nlinarith only [h.2, hquery]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery



theorem Refines.bind {ι α β : Type*} {relation : α → ℚ → Prop}
    {nextRelation : β → ℚ → Prop} {program : BitQuery ι α} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (next : α → BitQuery ι β) (expectedNext : ℚ → FiniteQuery ι)
    (hn : ∀ a v, relation a v → Refines nextRelation (next a) (expectedNext v)) :
    Refines nextRelation (program.bind next) (FiniteQuery.bind expected expectedNext) := by
  induction h with
  | done h => exact hn _ _ h
  | read key continuation expected h ih => exact .read key _ _ ih
  | charge steps h ih => exact .charge steps ih



theorem Refines.collect {ι κ β : Type*} {relation : β → ℚ → Prop}
    (reader : κ → BitQuery ι BinaryFraction) (expectedReader : κ → FiniteQuery ι)
    (hr : ∀ key, Refines (fun word value => word.value = value) (reader key) (expectedReader key))
    (inputs : List κ) (next : List BinaryFraction → BitQuery ι β)
    (expectedNext : List ℚ → FiniteQuery ι)
    (hn : ∀ words, Refines relation (next words) (expectedNext (words.map BinaryFraction.value))) :
    Refines relation (BitQuery.collect reader inputs next)
      (FiniteQuery.collect expectedReader inputs expectedNext) := by
  induction inputs generalizing next expectedNext with
  | nil => exact hn []
  | cons key inputs ih =>
    apply (hr key).bind
    intro word value hv
    subst value
    apply Refines.charge
    apply ih
    intro words
    exact hn (word :: words)

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





theorem queryEraseLoopWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1 = List.eraseDupsBy.loop (· == ·) xs seen := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    have ht : (memberByWithWork equal a seen).1 = seen.any (a == ·) := by
      apply Bool.eq_iff_iff.mpr
      simp only [memberByWithWork_value equal heq, List.any_eq_true, beq_iff_eq]
      exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hab⟩ => hab ▸ hb⟩
    simp only [queryEraseLoopWithWork, ht, ih, List.eraseDupsBy.loop]
    cases seen.any (a == ·) <;> rfl

@[simp] theorem queryEraseWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1 = xs.eraseDups :=
  queryEraseLoopWithWork_value equal heq xs []

theorem queryEraseLoopWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) (hs : seen.Nodup) :
    (queryEraseLoopWithWork equal xs seen).1.Nodup := by
  induction xs generalizing seen with
  | nil => simpa only [queryEraseLoopWithWork, List.nodup_reverse] using hs
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.Nodup
    by_cases h : (memberByWithWork equal a seen).1 = true
    · rw [ite_eq_left h]
      exact ih seen hs
    · rw [ite_eq_right h]
      apply ih
      exact List.nodup_cons.mpr ⟨fun ha => h ((memberByWithWork_value equal heq a seen).mpr ha), hs⟩

theorem queryEraseWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1.Nodup :=
  queryEraseLoopWithWork_nodup equal heq xs [] (by simp)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted insertion sorting for the distinct-key lists. The numerical
encoding determines exactly the order used by the reference query. -/

namespace EditApproximation





theorem queryInsertWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).1 = List.orderedInsert r a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [queryInsertWithWork, hle, List.orderedInsert_cons, decide_eq_true_eq]
    split <;> simp only [ih]

theorem querySortWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b)) (xs : List α) :
    (querySortWithWork le xs).1 = xs.insertionSort r := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [querySortWithWork, queryInsertWithWork_value r le hle, ih, List.insertionSort_cons]



theorem queryOrderedInputsWithWork_value {α : Type*} [DecidableEq α]
    (encode : α → ℕ) (hinjective : Function.Injective encode)
    (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b)) (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).1 = orderedInputs encode hinjective xs.toFinset := by
  let : LinearOrder α := LinearOrder.lift' encode hinjective
  have hle' : ∀ a b, (le a b).1 = decide (a ≤ b) := hle
  rw [queryOrderedInputsWithWork, querySortWithWork_value (· ≤ ·) le hle',
    queryEraseWithWork_value equal heq]
  have hd := queryEraseWithWork_nodup equal heq xs
  rw [queryEraseWithWork_value equal heq] at hd
  have hn : (xs.eraseDups.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) xs.eraseDups).nodup_iff.mpr hd
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr
    (List.pairwise_insertionSort (· ≤ ·) xs.eraseDups)
  have hf : (xs.eraseDups.insertionSort (· ≤ ·)).toFinset = xs.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_insertionSort, List.mem_eraseDups]
  rw [hf] at hs
  exact hs.symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputCodes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



theorem queryEncodedLEWithWork_value {α : Type*} (code : α → ℕ × ℕ) (a b : α) :
    (queryEncodedLEWithWork code a b).1 = decide ((code a).1 ≤ (code b).1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryEncodedLEWithWork, wordLEWithWork_value, bitWordValue_bits, decide_eq_true_eq]



@[simp] theorem queryOrderedChildInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1 =
      orderedInputs childInputCode (childInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value childInputCode (childInputCode_injective M n)
    _ _ coordinateEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value]



@[simp] theorem queryOrderedHistoryInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1 =
      orderedInputs historyInputCode (historyInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value historyInputCode (historyInputCode_injective M n)
    _ _ queryHistoryEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActionInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Once the selected group and online actions have been computed, the
last adaptive gather lists exactly their child coordinates, sorted by
the same injective encoding as the reference query. -/

namespace EditApproximation

theorem query_mem_action_cover {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M)) (input : Child) :
    input ∈ actionCurrentInputCover actions ↔
      ∃ action ∈ actions, ∃ i, action.childState i = input := by
  constructor
  · intro h
    obtain ⟨index, _, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hi
    exact ⟨actions.get index, List.get_mem actions index, i, heq⟩
  · rintro ⟨action, ha, i, rfl⟩
    exact actionCurrentInputCover_mem actions action ha i



theorem queryActionInputsWithWork_value {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (queryActionInputsWithWork actions).1.toFinset =
      actionCurrentInputCover (actions.map BinaryBellmanAction.decode) := by
  ext input
  simp only [queryActionInputsWithWork, arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, query_mem_action_cover]
  constructor
  · rintro ⟨action, ha, i, hi⟩
    exact ⟨action.decode, ⟨action, ha, rfl⟩, i, hi⟩
  · rintro ⟨action, ⟨word, hw, rfl⟩, i, hi⟩
    exact ⟨word, hw, i, hi⟩



theorem queryNeededInputsWithWork_value {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M)) :
    (queryNeededInputsWithWork selected online).1 =
      orderedInputs childInputCode (childInputCode_injective M n)
        (actionCurrentInputCover (selected.map BinaryBellmanAction.decode) ∪
         actionCurrentInputCover (online.map BinaryBellmanAction.decode)) := by
  simp only [queryNeededInputsWithWork, queryOrderedChildInputsWithWork_value,
    List.toFinset_append, queryActionInputsWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawCentersWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryRawCentersWithWork N P F a value q).1 =
      rawRefinementCenters N P F a.value value.value q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P)
      ⌈value.value⌉₊ q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  simp only [queryRawCentersWithWork, queryEraseWithWork_value _ queryIntervalEqualWithWork_value,
    arithmeticFlatMapWithWork_value, seedGridSpacingWithWork_value _ _ hP,
    naturalCeilingWithWork_value, hg, queryScalesWithWork_value, rawRefinementCenters]



@[simp] theorem queryInitialSupportWithWork_value {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1 =
      refinementInitialSupport N P F exponent a.value value.value q := by
  simp only [queryInitialSupportWithWork, queryRawCentersWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value _ _ hP, canonicalMulWithWork_value, inversePowerTwo_value,
    nat_value, queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    localOnlineSourceKeys, List.map_map, refinementInitialSupport]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted representative and child-coordinate lists for adaptive band
data gathers. All initial-table lookups are included in the work counter. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryEarlierRepresentativesWithWork_value {n : ℕ} (N P F exponent : ℕ)
    (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (q : TargetInterval n) (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1 =
      queryEarlierRepresentatives N P F exponent a.value (fun r => (initial r).1.value) q := by
  have hl := (localRepresentativeReadWithWork_eq_cost N P F a initial q R hR).1
  have hc (b : ℕ) (cell : ℕ × ℕ) :=
    (cellCentersReadWithWork_eq_cost P F b a (inversePowerTwo exponent) initial cell R hR).1
  simp only [queryEarlierRepresentativesWithWork, hl, hc, localRepresentativesWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    cellCentersWithWork_value _ _ _ _ _ _ _ hP, inversePowerTwo_value,
    queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    queryEarlierRepresentatives, localGroupQueryKeys, localOnlineSourceKeys]



@[simp] theorem queryWideInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryWideInputsWithWork M parent P representatives).1 = wideWarmupInputs parent P representatives := by
  simp only [queryWideInputsWithWork, queryEraseWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    wideChildGridWithWork_value _ _ _ _ _ hP, wideWarmupInputs]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The earlier-history cover is materialized from its small coordinate
lists, then sorted by the original history encoding. It never enumerates
the much larger Cartesian set of complete wide actions. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryRawHistoryInputsWithWork_cover {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P history : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.toFinset =
      wideEarlierInputCover parent P history representatives := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_range, List.mem_map, wideEarlierInputCover, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_range, Finset.mem_image]



theorem queryEarlierInputsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1 =
      orderedInputs historyInputCode (historyInputCode_injective M ny)
        (queryEarlierInputCover parent N P F exponent history a.value
          (fun r => (initial r).1.value) q) := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value,
    queryRawHistoryInputsWithWork_cover _ _ _ _ hP,
    queryEarlierRepresentativesWithWork_value _ _ _ _ hP _ _ _ R hR, queryEarlierInputCover]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySharedInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The shared-current request list is built from counted whole-cell
enumerations and sorted by the original child encoding. -/

namespace EditApproximation



namespace BinaryFraction



theorem querySharedInputsWithWork_value {α : Type*} (source target : List α)
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (parent : TargetInterval source.length) (a value : BinaryFraction)
    (query : TargetInterval target.length) (draw : CountedCellGroupDraws M F Q) :
    (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a value query draw).1 =
      orderedInputs childInputCode (childInputCode_injective M target.length)
        (querySharedInputCover source target parent N F exponent Q a.value (fun _ => value.value) query
          (fun b cell scale sample => (draw b cell scale sample).1)) := by
  have hc (e : ℕ) (cell : ℕ × ℕ) (input : Fin M × TargetInterval target.length) :
      input ∈ (querySharedCellInputsWithWork (ny := target.length) M F Q eM e eF hM hF parent
        exponent cell (draw (2 ^ e) cell)).1 ↔
      ∃ scale, input ∈ groupCurrentInputCover source target parent (2 ^ e) exponent Q cell
        (groupDyadicScaleAt M (2 ^ e) F scale) (fun sample => (draw (2 ^ e) cell scale sample).1) := by
    rw [← List.mem_toFinset, querySharedCellInputsWithWork_value source target]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  simp only [querySharedInputsWithWork, queryOrderedChildInputsWithWork_value]
  apply congrArg (orderedInputs childInputCode (childInputCode_injective M target.length))
  unfold querySharedInputCover localGroupQueryKeys
  rw [← queryExponentsWithWork_value N F a value]
  ext input
  simp only [arithmeticFlatMapWithWork_value, targetCellsWithWork_value,
    canonicalMulWithWork_value, inversePowerTwo_value, nat_value, naturalCeilingWithWork_value,
    List.mem_toFinset, List.mem_flatMap, List.flatMap_map, List.mem_map, Finset.mem_biUnion,
    Finset.mem_univ, true_and, hc]
  aesop

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementGather
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The last three adaptive gathers of a refinement request. Each request
list is constructed after the answers on which it depends. The selected
actions, list construction, sorting and buffer cells all carry work. -/

namespace EditApproximation

section Simulation
variable {ι β α : Type*} {relation : β → ℚ → Prop}
  (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (expectedOnline : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (expectedSelected : List (Fin M × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M))
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
  (expectedNext : List (Fin M × ℕ × TargetInterval target.length) → List ℚ →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (RationalBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List ℚ → FiniteQuery ι)

theorem queryRefinementGather_refines_oai
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hc : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key))
    (ho : ∀ keys words, ((online keys words).1.map BinaryBellmanAction.decode) =
      expectedOnline keys (words.map BinaryFraction.value))
    (hs : ∀ keys words, ((selected keys words).1.map BinaryBellmanAction.decode) =
      expectedSelected keys (words.map BinaryFraction.value))
    (hn : ∀ earlierKeys earlierWords groups actions keys words,
      BitQuery.Refines relation (next earlierKeys earlierWords groups actions keys words)
        (expectedNext earlierKeys (earlierWords.map BinaryFraction.value)
          (groups.map BinaryBellmanAction.decode) (actions.map BinaryBellmanAction.decode)
          keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
        a t initial draw q readEarlier readCurrent online selected next)
      (let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length)
          (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
       FiniteQuery.collect expectedEarlier earlierKeys fun earlierWords =>
         let actions := expectedOnline earlierKeys earlierWords
         let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length)
           (querySharedInputCover source target parent N F exponent Q a.value
             (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
         FiniteQuery.collect expectedCurrent sharedKeys fun sharedWords =>
           let groups := expectedSelected sharedKeys sharedWords
           let keys := orderedInputs childInputCode (childInputCode_injective M target.length)
             (actionCurrentInputCover groups ∪ actionCurrentInputCover actions)
           FiniteQuery.collect expectedCurrent keys
             (expectedNext earlierKeys earlierWords groups actions keys)) := by
  have hshared : querySharedInputCover source target parent N F exponent Q a.value
      (fun _ => (initial q).1.value) q (fun b cell scale sample => (draw b cell scale sample).1) =
      querySharedInputCover source target parent N F exponent Q a.value
        (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1) := rfl
  unfold queryRefinementGather
  dsimp only [BitQuery.compute, BitQuery.bind]
  apply BitQuery.Refines.charge
  rw [BinaryFraction.queryEarlierInputsWithWork_value M parent N P F exponent t hP a initial q R hR]
  apply BitQuery.Refines.collect readEarlier expectedEarlier he
  intro earlierWords
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  rw [BinaryFraction.querySharedInputsWithWork_value source target, hshared]
  apply BitQuery.Refines.collect readCurrent expectedCurrent hc
  intro sharedWords
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.charge
  rw [queryNeededInputsWithWork_value, ho, hs]
  apply BitQuery.Refines.collect readCurrent expectedCurrent hc
  intro words
  let ek := orderedInputs historyInputCode (historyInputCode_injective M target.length)
    (queryEarlierInputCover parent N P F exponent t a.value (fun r => (initial r).1.value) q)
  let sk := orderedInputs childInputCode (childInputCode_injective M target.length)
    (querySharedInputCover source target parent N F exponent Q a.value
      (fun r => (initial r).1.value) q (fun b cell scale sample => (draw b cell scale sample).1))
  let ck := orderedInputs childInputCode (childInputCode_injective M target.length)
    (actionCurrentInputCover (expectedSelected sk (sharedWords.map BinaryFraction.value)) ∪
      actionCurrentInputCover (expectedOnline ek (earlierWords.map BinaryFraction.value)))
  have hnext := hn ek earlierWords (selected sk sharedWords).1 (online ek earlierWords).1 ck words
  simpa only [ek, sk, ck, ho, hs] using hnext

end Simulation
end EditApproximation

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.EditApproximation.queryRefinementGather_refines_oai.{u_1, u_2, u_3} := @OAI.EditApproximation.queryRefinementGather_refines_oai.{u_1, u_2, u_3}
