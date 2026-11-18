-- Prove2me | solution 1 for OAI.EditApproximation.queryFamilyBoundedActive_refines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:35:28.199205+00:00
-- url     : https://prove2.me/submissions/0ab44200-689b-4374-aec7-716c2ddf7ff3

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
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
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_queryLocalRandomSources_refines

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_value {κ : Type*} [DecidableEq κ]
    (equal : κ → κ → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).1.value =
      finiteAnswerTable keys (values.map BinaryFraction.value) query := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, finiteAnswerTable, nat_value, Nat.cast_zero]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork, List.map_nil, finiteAnswerTable, nat_value, Nat.cast_zero]
    | cons value values =>
      simp only [gatheredWordLookupWithWork, List.map_cons, finiteAnswerTable]
      by_cases h : query = key
      · rw [ite_eq_left ((heq query key).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hx => h ((heq query key).mp hx)), ite_eq_right h]
        exact ih values

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQueryKeys
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Key tagging and finite-domain restriction preserve the adaptive
reference program. Executed key tests carry their actual Boolean cost. -/

namespace EditApproximation.BitQuery



theorem Refines.mapKeysWithWork {ι κ β : Type*} {relation : β → ℚ → Prop}
    (f : ι → κ × ℕ) (g : ι → κ) (hf : ∀ key, (f key).1 = g key)
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) :
    Refines relation (mapKeysWithWork f program) (FiniteQuery.mapKeys g expected) := by
  induction h with
  | done h => exact .done h
  | charge steps h ih => exact .charge steps ih
  | read key next expected h ih =>
    apply Refines.charge
    change Refines relation (.read (f key).1 _) (.read (g key) _)
    rw [hf key]
    exact .read _ _ _ ih



theorem Refines.restrictWithWork {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : Refines (fun word value => word.value = value) program expected) :
    Refines (fun word value => word.value = value)
      (restrictWithWork P test htest program) (FiniteQuery.restrict P expected) := by
  induction h with
  | done h => exact .done h
  | charge steps h ih => exact .charge steps ih
  | read key next expected h ih =>
    apply Refines.charge
    change Refines _ (dite ((test key).1 = true) _ _) (dite (P key) _ _)
    by_cases hp : P key
    · have ht := (htest key).mpr hp
      rw [dite_eq_left ht, dite_eq_left hp]
      exact .read _ _ _ ih
    · have ht : (test key).1 ≠ true := fun ht => hp ((htest key).mp ht)
      rw [dite_eq_right ht, dite_eq_right hp]
      simpa only [BinaryFraction.nat_value, Nat.cast_zero] using ih (BinaryFraction.nat 0)

end EditApproximation.BitQuery

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialGather
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The first adaptive gather executes its binary support construction
after reading the parent value, then requests those keys in their original
order. Its continuation receives only the stored words actually read. -/

namespace EditApproximation



theorem queryInitialGather_refines {ι β : Type*} {n : ℕ} {relation : β → ℚ → Prop}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (expectedReader : TargetInterval n → FiniteQuery ι)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (TargetInterval n) → List ℚ → FiniteQuery ι)
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (reader key) (expectedReader key))
    (hn : ∀ (value : BinaryFraction) (words : List BinaryFraction), BitQuery.Refines relation
      (next (refinementInitialSupport N P F exponent a.value value.value q) words)
      (expectedNext (refinementInitialSupport N P F exponent a.value value.value q)
        (words.map BinaryFraction.value))) :
    BitQuery.Refines relation (queryInitialGather N P F exponent hP a q reader next)
      (FiniteQuery.bind (expectedReader q) fun value =>
        let keys := refinementInitialSupport N P F exponent a.value value q
        FiniteQuery.collect expectedReader keys (expectedNext keys)) := by
  apply (hr q).bind
  intro value expected hv
  subst expected
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect reader _ _) _
  rw [BinaryFraction.queryInitialSupportWithWork_value]
  exact BitQuery.Refines.collect reader expectedReader hr _ _ _ (hn value)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
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



theorem queryBandInputsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryBandInputsWithWork M parent N P F exponent hP a initial q).1 =
      refinementBandInputList parent N P F exponent a.value (fun r => (initial r).1.value) q := by
  simp only [queryBandInputsWithWork, queryWideInputsWithWork_value _ _ _ hP,
    queryEarlierRepresentativesWithWork_value _ _ _ _ hP _ _ _ R hR, refinementBandInputList]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBandGather
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The band-data stage constructs its keys by counted Boolean routines,
then gathers mass and initial words in the reference order. -/

namespace EditApproximation



theorem queryBandGather_refines {ι β : Type*} {nx ny : ℕ} {relation : β → ℚ → Prop}
    (M : ℕ) (parent : TargetInterval nx) (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (expectedMass expectedInitial : (Fin M × TargetInterval ny) → FiniteQuery ι)
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction →
      BitQuery ι β)
    (expectedNext : List (Fin M × TargetInterval ny) → List ℚ → List ℚ → FiniteQuery ι)
    (hm : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (massReader key) (expectedMass key))
    (hi : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (initialReader key) (expectedInitial key))
    (hn : ∀ mass words,
      let keys := refinementBandInputList (M := M) parent N P F exponent a.value
        (fun r => (initial r).1.value) q
      BitQuery.Refines relation (next keys mass words)
        (expectedNext keys (mass.map BinaryFraction.value) (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next)
      (let keys := refinementBandInputList (M := M) parent N P F exponent a.value
        (fun r => (initial r).1.value) q
       FiniteQuery.collect expectedMass keys fun mass =>
         FiniteQuery.collect expectedInitial keys (expectedNext keys mass)) := by
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect massReader _ _) _
  rw [BinaryFraction.queryBandInputsWithWork_value M parent N P F exponent hP a initial q R hR]
  apply BitQuery.Refines.collect massReader expectedMass hm
  intro mass
  exact BitQuery.Refines.collect initialReader expectedInitial hi _ _ _ (hn mass)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedBody
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite-domain guards execute binary comparisons on table coordinates.
Random-source coordinates pass through the guard unchanged. -/

namespace EditApproximation

section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})





theorem queryRestrictPhysicalBody_refines
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (expected : (request : PhysicalTableRequest M J n) →
      FiniteQuery (Sum σ {child : PhysicalTableRequest M J n //
        child.combinedRank T S < request.combinedRank T S}))
    (h : BitQuery.Refines (fun word value => word.value = value) program (expected parent.val)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryRestrictPhysicalBody passes copies T S parent program)
      (SourceRanked.restrictBody (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) expected parent) := by
  classical
  exact (h.restrictWithWork _ _ (querySupportedChildWithWork_value passes copies T S parent)).mapKeysWithWork
    _ _ (fun _ => rfl)

end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



namespace BinaryFraction



@[simp] theorem queryOnlineIntegerReadWithWork_value {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    (queryOnlineIntegerReadWithWork keys values b q).1 =
      ⌊finiteAnswerTable keys (values.map value) (b, q)⌋₊ := by
  simp only [queryOnlineIntegerReadWithWork, naturalFloorWithWork_value,
    gatheredWordLookupWithWork_value _ queryOnlineKeyEqualWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryChildReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × TargetInterval n)) (values : List BinaryFraction)
    (i : Fin M) (q : TargetInterval n) :
    (queryChildReadWithWork keys values i q).1.value =
      finiteAnswerTable keys (values.map value) (i, q) :=
  gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value keys values (i, q)



@[simp] theorem queryHistoryReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) :
    (queryHistoryReadWithWork keys values s input).1.value =
      finiteAnswerTable keys (values.map value) (input.1, s, input.2) :=
  gatheredWordLookupWithWork_value _ queryHistoryEqualWithWork_value keys values (input.1, s, input.2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalScalarReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Concrete scalar-source adapters.  Guards, finite source addresses and
tag construction are executed before each read; rejected requests return
the original zero value without exposing a random coordinate. -/

namespace EditApproximation

section Scalar
variable (M J N n exponent F Q R B : ℕ)





theorem queryPhysicalScalarRead_refines (key : PhysicalScalarKey M J N n exponent F Q R B) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarRead M J N n exponent F Q R B key) (.read key .done) :=
  .charge _ (.read key _ _ (fun _ => .done rfl))







private theorem queryGroup_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (expected : PhysicalGroupQueries M J N n exponent F Q R B b)
    (he : ∀ scale sample, BitQuery.Refines (fun word value => word.value = value)
      (actual scale sample) (expected scale sample)) :
    ∀ scale sample, BitQuery.Refines (fun word value => word.value = value)
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) scale sample)
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) expected) scale sample) := by
  subst c
  exact he

theorem queryPhysicalScalarGroupRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key)
      (physicalScalarGroupRead M J N n exponent F Q R B node time key) := by
  apply BitQuery.Refines.charge
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold queryPhysicalScalarGroupQueries physicalScalarGroupRead physicalScalarGroupQueries
  dsimp only
  by_cases hb : b ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left ((queryScalePresentWithWork_value N b).mpr hb)]
    by_cases hc : cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent
    · rw [dite_eq_left hc, dite_eq_left ((queryCellValidWithWork_value n exponent cell).mpr hc)]
      exact queryGroup_transport M J N n exponent F Q R B _ b (physicalScaleIndex_get N b hb)
        _ _ (fun _ _ => queryPhysicalScalarRead_refines M J N n exponent F Q R B _) scale sample
    · rw [dite_eq_right hc, dite_eq_right
        (fun h => hc ((queryCellValidWithWork_value n exponent cell).mp h))]
      exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])
  · rw [dite_eq_right hb, dite_eq_right
      (fun h => hb ((queryScalePresentWithWork_value N b).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])



theorem queryPhysicalScalarOnlineRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range)
      (physicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  apply BitQuery.Refines.charge
  unfold physicalScalarOnlineRead
  by_cases hb : key.1 ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left ((queryScalePresentWithWork_value N key.1).mpr hb)]
    by_cases hr : 0 < range ∧ range ≤ B
    · rw [dite_eq_left hr, dite_eq_left ((queryRangeValidWithWork_value B range).mpr hr)]
      exact queryPhysicalScalarRead_refines M J N n exponent F Q R B _
    · rw [dite_eq_right hr, dite_eq_right (fun h => hr ((queryRangeValidWithWork_value B range).mp h))]
      exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])
  · rw [dite_eq_right hb, dite_eq_right (fun h => hb ((queryScalePresentWithWork_value N key.1).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])

end Scalar
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyScalarReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted pass/copy indexing for the independent scalar family.  Both
remainders and the complete family address are computed before lookup. -/

namespace EditApproximation



theorem queryFinOfNatWithWork_value (bound value : ℕ) (hb : 0 < bound) [NeZero bound] :
    (queryFinOfNatWithWork bound value hb).1 = Fin.ofNat bound value := by
  apply Fin.ext
  exact (binaryNaturalDivModWithWork_spec value bound hb).2

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)



theorem queryFamilyTagWithWork_value
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).1 =
      (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, scalar) := by
  simp only [queryFamilyTagWithWork, queryFinOfNatWithWork_value]



theorem queryFamilyGroupRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key)
      (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key) := by
  exact (queryPhysicalScalarGroupRead_refines M J N target.length exponent F Q R
    (localOnlineMassBound M P H) node time key).mapKeysWithWork _ _
      (queryFamilyTagWithWork_value target N P F exponent H Q passes copies pass copy)



theorem queryFamilyOnlineRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range)
      (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range) := by
  exact (queryPhysicalScalarOnlineRead_refines M J N target.length exponent F Q R
    (localOnlineMassBound M P H) node time key range).mapKeysWithWork _ _
      (queryFamilyTagWithWork_value target N P F exponent H Q passes copies pass copy)

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryParentReadWithWork_value {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).1.value = finiteAnswerTable keys (words.map value) r :=
  gatheredWordLookupWithWork_value _ queryIntervalEqualWithWork_value keys words r

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass and initial words are read into counted finite buffers before
any random source range or local action is constructed. -/

namespace EditApproximation

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

theorem queryLocalBand_refines
    (expectedMass expectedInitial : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hm : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readMass key) (expectedMass key))
    (hi : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readInitial key) (expectedInitial key))
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger
        q readEarlier readCurrent)
      (localRandomBandDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) := by
  classical
  let Rp := ∑ r, (parentInitial r).2
  have hp : ∀ r, (parentInitial r).2 ≤ Rp := fun r =>
    Finset.single_le_sum (f := fun r => (parentInitial r).2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  unfold queryLocalBand localRandomBandDataQuery
  apply queryBandGather_refines M parent N P F exponent hP a parentInitial q Rp hp
    readMass readInitial expectedMass expectedInitial
    (expectedNext := fun keys massWords initialWords =>
      localRandomSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value)
        (fun i r => finiteAnswerTable keys massWords (i, r))
        (fun i r => finiteAnswerTable keys initialWords (i, r)) q
        expectedGroup expectedInteger expectedEarlier expectedCurrent)
    (hm := hm) (hi := hi)
  intro massWords initialWords
  let keys := refinementBandInputList (M := M) parent N P F exponent a.value
    (fun r => (parentInitial r).1.value) q
  have h := queryLocalRandomSources_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial
    (BinaryFraction.queryChildReadWithWork keys massWords)
    (BinaryFraction.queryChildReadWithWork keys initialWords)
    (BinaryFraction.queryDataReadBudget M target.length keys)
    (BinaryFraction.queryChildReadWithWork_budget keys massWords)
    (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
    q readGroup readInteger readEarlier readCurrent expectedGroup expectedInteger expectedEarlier
    expectedCurrent hg hz he hr
  simpa only [BinaryFraction.queryChildReadWithWork_value] using h

end Band
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete adaptive local program, beginning with the parent query.
Every intermediate buffer is constructed after the answers determining
its support, and every scalar source range is computed before its read. -/

namespace EditApproximation

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

theorem queryLocalProgram_refines
    (expectedParent : TargetInterval target.length → FiniteQuery ι)
    (expectedMass expectedInitial : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hp : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readParent key) (expectedParent key))
    (hm : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readMass key) (expectedMass key))
    (hi : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readInitial key) (expectedInitial key))
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t readParent readMass readInitial readGroup readInteger
        q readEarlier readCurrent)
      (localRandomDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        expectedParent expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) := by
  unfold queryLocalProgram localRandomDataQuery
  apply queryInitialGather_refines N P F exponent hP a q readParent expectedParent
    (expectedNext := fun keys words =>
      localRandomBandDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (finiteAnswerTable keys words) expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) (hr := hp)
  intro value words
  let keys := refinementInitialSupport N P F exponent a.value value.value q
  have h := queryLocalBand_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t (BinaryFraction.queryParentReadWithWork keys words)
    readMass readInitial readGroup readInteger q readEarlier readCurrent
    expectedMass expectedInitial expectedGroup expectedInteger expectedEarlier expectedCurrent
    hm hi hg hz he hr
  simpa only [BinaryFraction.queryParentReadWithWork_value] using h

end Program
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryMeanRead
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted averaging of the warmup words actually requested. The fixed
requested denominator is retained even in the simulation of arbitrary
intermediate answer lists. -/

namespace EditApproximation



theorem queryMeanRead_refines {ι : Type*} (count : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction) (expected : Fin count → FiniteQuery ι)
    (hr : ∀ i, BitQuery.Refines (fun word value => word.value = value) (reader i) (expected i)) :
    BitQuery.Refines (fun word value => word.value = value) (queryMeanRead count reader)
      (FiniteQuery.collect expected (List.ofFn fun i : Fin count => i)
        (fun words => .done (words.sum / count))) := by
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.collect reader expected hr
  intro words
  exact .charge _ (.done (BinaryFraction.queryMeanWithWork_value count words))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalReaders
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual ranked physical reads for the charged local program.  Table
addresses are constructed before lookup, mass reads execute their mean,
and the total history reader executes its natural-word guard. -/

namespace EditApproximation



theorem queryPhysicalTableRead_refines {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalTableRead copies T S parent child) (.read child .done) :=
  .charge _ (.read child _ _ (fun _ => .done rfl))



theorem queryPhysicalWarmupRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (q : TargetInterval n)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalWarmupRead copies pass copy T S t ht node q otherNode hnode j hj r)
      (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r) :=
  queryPhysicalTableRead_refines copies T S _ _



theorem queryPhysicalMassRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input)
      (physicalRefinementMassQuery pass copy T S t ht node hbelow q input) :=
  queryMeanRead_refines T _ _ (fun _ => queryPhysicalWarmupRead_refines copies pass copy T S t ht
    node q _ _ _ _ _)



theorem queryPhysicalCurrentRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input)
      (physicalRefinementCurrentQuery pass copy T S t node hbelow q input) :=
  queryPhysicalTableRead_refines copies T S _ _



theorem queryPhysicalEarlierRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × ℕ × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input)
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input) := by
  unfold queryPhysicalEarlierRead
  apply BitQuery.Refines.charge
  unfold physicalRefinementEarlierQuery
  by_cases hs : input.2.1 < t
  · rw [dite_eq_left hs, dite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr hs)]
    exact queryPhysicalTableRead_refines copies T S _ _
  · rw [dite_eq_right hs, dite_eq_right (fun h => hs ((binaryNaturalCompareWithWork_lt _ _).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full charged refinement program on physical ranked requests and
scalar source requests.  This connects the local Boolean implementation
to the same adaptive query used in the accuracy and dependency proofs. -/

namespace EditApproximation

section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)

theorem queryPhysicalRandomDataRequest_refines
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q)
      (physicalRandomDataRequestQuery source target N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value pass copy T S t ht node hbelow
        expectedGroup expectedInteger q) := by
  unfold queryPhysicalRandomDataRequest physicalRandomDataRequestQuery
  apply queryLocalProgram_refines
  · intro r
    exact (queryPhysicalWarmupRead_refines copies pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r).mapKeysWithWork _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalMassRead_refines copies pass copy T S t ht node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalWarmupRead_refines copies pass copy T S t ht node q
      (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2).mapKeysWithWork _ _ (fun _ => rfl)
  · intro key
    exact (hg key).mapKeysWithWork _ _ (fun _ => rfl)
  · intro key range
    exact (hz key range).mapKeysWithWork _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalEarlierRead_refines copies pass copy T S t node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)
  · intro input
    exact (queryPhysicalCurrentRead_refines copies pass copy T S t node hbelow q input).mapKeysWithWork
      _ _ (fun _ => rfl)

end Physical
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged local refinement uses the independent source
family, with computed scalar guards and pass/copy addresses. -/

namespace EditApproximation

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R)
  (q : TargetInterval target.length)

theorem queryFamilyRefinement_refines :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        passes copies pass copy T S t ht node hbelow time q)
      (physicalRandomDataRequestQuery source target N P F exponent H Q tau.value a.value eta.value
        kappa.value delta.value pass copy T S t ht node hbelow
        (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q) := by
  apply queryPhysicalRandomDataRequest_refines
  · intro key
    exact queryFamilyGroupRead_refines target N P F exponent H Q passes copies pass copy _ time key
  · intro key range
    exact queryFamilyOnlineRead_refines target N P F exponent H Q passes copies pass copy _ time key range

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyActive
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive internal refinement steps expose exactly the independent
scalar family and smaller physical table requests of the reference body. -/

namespace EditApproximation

section Active
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)

theorem queryFamilyActive_refines (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (ha : a.value = refinementFactor (factor request.pass) F)
    (hlong : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        T S passes copies request hindex hbelow)
      (physicalRandomGlobalQuery (R := R) source target N P F exponent H Q T S copies factor multiplier
        tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial request) := by
  unfold queryFamilyActive physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hlong⟩]
  apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
  simpa only [ha] using queryFamilyRefinement_refines (R := R) source target N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta passes copies request.pass request.copy T S
    (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
    (Fin.ofNat R (request.index - T - 1)) request.state

end Active

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

theorem queryFamilyBoundedActive_refines_oai (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (ha : a.value = refinementFactor (factor parent.val.pass) F)
    (hlong : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        T S passes copies parent hindex hbelow)
      (physicalRandomBoundedQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies factor multiplier
        tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial parent) := by
  apply queryRestrictPhysicalBody_refines
  exact queryFamilyActive_refines (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow factor multiplier initial ha hlong

end Bounded
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.queryFamilyBoundedActive_refines_oai.{u_1} := @OAI.EditApproximation.queryFamilyBoundedActive_refines_oai.{u_1}
