-- Prove2me | solution 1 for OAI.EditApproximation.queryChargedFamilyTable_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:35:03.896217+00:00
-- url     : https://prove2.me/submissions/97a71c3f-169b-4648-8fea-359793f89d08

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
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_localWarmupKernelWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_queryPhysicalInitial_width

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le_storageBits (n : ℕ) : (nat n).width ≤ (nat n).representation.storageBits := by
  rw [nat_representation]
  have hw : (nat n).width = max (Nat.size n) 1 := by
    simp only [nat, width, SignedBinary.ofInt, Int.natAbs_natCast, ← Nat.size_eq_bits_len,
      List.length_cons, List.length_nil]
  rw [hw]
  simp only [UnreducedRational.nat, UnreducedRational.storageBits, Int.natAbs_natCast, Nat.size_one]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

theorem storageBits_nat (n : ℕ) : (nat n).storageBits = Nat.size n + 2 := by
  simp [nat, storageBits]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUpdateWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the actual coordinate update, including construction of
its rational step and complement. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le (n : ℕ) : (nat n).width ≤ Nat.size n + 2 := by
  have h := nat_width_le_storageBits n
  rw [nat_representation, UnreducedRational.storageBits_nat] at h
  exact h

end BinaryFraction
end EditApproximation

end OAI
end

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBellmanReads
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Bellman action evaluation with literal finite-table reader calls.
Child words are gathered once, then Boolean arithmetic
operates on that stored list. Reader scans are part of the returned cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem bellmanActionReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) :
    (bellmanActionReadWithWork distance L read query action).1 =
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).1 := by
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]



theorem bellmanReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (bellmanReadWithWork distance L fallback read query actions).1 =
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).1 := by
  simp only [bellmanReadWithWork, bellmanWithWork, arithmeticMapWithWork_value,
    bellmanActionReadWithWork_eq]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_width {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (B : ℕ) (hB : 2 ≤ B) (hvalues : ∀ value ∈ values, value.width ≤ B) :
    (gatheredWordLookupWithWork equal keys values query).1.width ≤ B := by
  induction keys generalizing values with
  | nil => exact (nat_width_le 0).trans (by simpa using hB)
  | cons key keys ih =>
    cases values with
    | nil => exact (nat_width_le 0).trans (by simpa using hB)
    | cons value values =>
      simp only [gatheredWordLookupWithWork]
      split_ifs
      · exact hvalues value List.mem_cons_self
      · exact ih values (fun v hv => hvalues v (List.mem_cons_of_mem _ hv))

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryWarmupReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The warmup continuation evaluates finite input-table lookups and
charges their scan costs at the point where each returned word is used. -/

namespace EditApproximation
namespace BinaryFraction



theorem localWarmupReadKernelWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (localWarmupReadKernelWithWork parent N P F a initial child query).1 =
      (localWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).1 := by
  have hr := (localRepresentativeReadWithWork_eq_cost N P F a initial query R hR).1
  simp only [localWarmupReadKernelWithWork, localWarmupKernelWithWork, hr, bellmanReadWithWork_eq]

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





theorem value_bind {ι α β : Type*} (oracle : ι → BinaryFraction)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)
  | charge steps continuation ih => exact ih

theorem value_collect {ι κ β : Type*} (oracle : ι → BinaryFraction)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).value oracle =
      (next (inputs.map fun key => (reader key).value oracle)).value oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key inputs ih => simp only [collect, value_bind, value, ih, List.map_cons]

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





theorem queryIntervalEqualWithWork_cost {n : ℕ} (a b : TargetInterval n)
    (B : ℕ) (hn : Nat.size n ≤ B) :
    (queryIntervalEqualWithWork a b).2 ≤ 16 * B + 5 := by
  have hl := naturalEqualWithWork_cost a.lo b.lo B
    ((Nat.size_le_size (a.ordered.trans a.valid)).trans hn)
    ((Nat.size_le_size (b.ordered.trans b.valid)).trans hn)
  have hh := naturalEqualWithWork_cost a.hi b.hi B
    ((Nat.size_le_size a.valid).trans hn) ((Nat.size_le_size b.valid).trans hn)
  change _ + _ + 1 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



theorem queryParentReadWithWork_cost {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).2 ≤ 1 + keys.length * (16 * Nat.size n + 6) := by
  exact gatheredWordLookupWithWork_cost queryIntervalEqualWithWork (16 * Nat.size n + 5)
    (fun a b => queryIntervalEqualWithWork_cost a b _ le_rfl) keys words r

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceWidths
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem mapKeysWithWork_value {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) :
    (mapKeysWithWork f program).value oracle = program.value (fun key => oracle (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih => exact ih (oracle (f key).1)

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryOverrideParentReadWithWork_cost {n : ℕ} (value : BinaryFraction)
    (q : TargetInterval n) (keys : List (TargetInterval n)) (words : List BinaryFraction)
    (r : TargetInterval n) :
    (queryOverrideParentReadWithWork value q keys words r).2 ≤
      16 * Nat.size n + 7 + keys.length * (16 * Nat.size n + 6) := by
  have ht := queryIntervalEqualWithWork_cost r q (Nat.size n) le_rfl
  have hr := queryParentReadWithWork_cost keys words r
  unfold queryOverrideParentReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega



end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupWidth
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

theorem queryWarmupProgram_width {ι : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F B : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (q : TargetInterval ny) (oracle : ι → BinaryFraction)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
    (hc : ∀ r, ((childRead r).value oracle).width ≤ B) :
    ((queryWarmupProgram parent N P F a initialRead childRead q).value oracle).width ≤
      localWarmupWordBudget M B := by
  let value := (initialRead q).value oracle
  let centers := queryRawCentersWithWork N P F a value q
  let words := centers.1.map fun r => (initialRead r).value oracle
  let initial := queryOverrideParentReadWithWork value q centers.1 words
  let inputs := queryWarmupInputsWithWork M parent N P F a initial q
  let childWords := inputs.1.map fun input => (childRead input).value oracle
  let child := fun input : Fin M × TargetInterval ny => queryChildReadWithWork inputs.1 childWords input.1 input.2
  have hiW : ∀ r, (initial r).1.width ≤ B := by
    intro r
    unfold initial queryOverrideParentReadWithWork
    dsimp only
    split_ifs
    · exact hi q
    · exact gatheredWordLookupWithWork_width _ centers.1 words r B (by omega) (by
        intro w hw
        obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
        exact hi key)
  have hcW : ∀ input, (child input).1.width ≤ B := by
    intro input
    exact gatheredWordLookupWithWork_width _ inputs.1 childWords input B (by omega) (by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hc key)
  have hw := (localWarmupKernelWithWork_bounds parent N P F B hP hFpos a
    (fun r => (initial r).1) (fun input => (child input).1) q hB hN hnx hny hM hPb hF ha hiW hcW).1
  rw [← localWarmupReadKernelWithWork_eq parent N P F a initial child q
    (16 * Nat.size ny + 7 + centers.1.length * (16 * Nat.size ny + 6))
    (queryOverrideParentReadWithWork_cost value q centers.1 words)] at hw
  simpa only [queryWarmupProgram, BitQuery.value_bind, BitQuery.value_collect,
    BitQuery.compute, BitQuery.value] using hw

theorem queryChargedWarmup_width (source target : List ℕ) {M J passes copies T S : ℕ}
    (N P F B : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
    (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) :
    ((queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).value
      oracle).width ≤ localWarmupWordBudget M B := by
  have hi (q : TargetInterval target.length) := queryPhysicalInitial_width source target N P F B A a
    multiplier parent occurrence symbolBits positionBits oracle q hP ht' hinit
  have hsmall : B ≤ localWarmupWordBudget M B := by
    unfold localWarmupWordBudget physicalContinuationInputBudget
    dsimp only
    omega
  unfold queryChargedWarmup
  simp only [BitQuery.value]
  split
  · exact (hi _).trans hsmall
  · split
    · split
      · exact (hi _).trans hsmall
      · exact queryWarmupProgram_width _ N P F B hP a _ _ _ oracle hB hN hF hFpos hPb hs ht hM ha hi
          (fun _ => hv _)
    · exact (hi _).trans hsmall

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedTableWidth
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF B : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)

theorem queryChargedFamilyTable_width_oai
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hMb : Nat.size M ≤ B) (ha : (a parent.val.pass).width ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hactive : ∀ (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J),
      ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
        tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow).value
        (fun key => oracle (Sum.map id (fun child =>
          ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key))).width ≤
        preparedKernelWordBudget M B) :
    ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget M B + preparedKernelWordBudget M B := by
  let tableOracle := fun key => oracle (Sum.inr key)
  have hw := queryChargedWarmup_width source target N P F B (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits tableOracle hB hP hN hPb hFb hFpos hs ht ht'
    hinit hMb ha hv
  have hi := queryPhysicalInitial_width source target N P F B (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits tableOracle parent.val.state hP ht' hinit
  have hsmall : B ≤ localWarmupWordBudget M B := by
    unfold localWarmupWordBudget physicalContinuationInputBudget
    dsimp only
    omega
  unfold queryChargedFamilyTable
  simp only [BitQuery.value]
  split
  · simp only [BitQuery.mapKeysWithWork_value]
    exact hw.trans (Nat.le_add_right _ _)
  · split
    · split
      · simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
        exact hi.trans (hsmall.trans (Nat.le_add_right _ _))
      · rename_i hindex hbelow hlong
        simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
        exact (hactive _ _).trans (Nat.le_add_left _ _)
    · simp only [BitQuery.value, BitQuery.mapKeysWithWork_value]
      exact hi.trans (hsmall.trans (Nat.le_add_right _ _))

end Table
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryChargedFamilyTable_width_oai := @OAI.EditApproximation.queryChargedFamilyTable_width_oai
