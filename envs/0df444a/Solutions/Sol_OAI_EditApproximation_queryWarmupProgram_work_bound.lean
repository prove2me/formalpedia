-- Prove2me | solution 1 for OAI.EditApproximation.queryWarmupProgram_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:31:13.480425+00:00
-- url     : https://prove2.me/submissions/0f8eee64-929b-4cf3-88a0-bfbc25097528

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea000
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_localWarmupKernelWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryRawCentersWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryWarmupInputsWithWork_bounds

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

theorem arithmeticMapWithWork_length_le_cost {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    xs.length ≤ (arithmeticMapWithWork f xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, arithmeticMapWithWork]; omega

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

theorem bellmanActionReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) (R : ℕ)
    (hread : ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanActionReadWithWork distance L read query action).2 ≤
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).2 + M * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun i => read (action.childState i))
    (List.finRange M) R (fun i _ => hread i)
  simp only [List.length_finRange] at h
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]
  omega



theorem bellmanReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (hread : ∀ action ∈ actions, ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanReadWithWork distance L fallback read query actions).2 ≤
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).2 +
        actions.length * (M * (R + 3)) := by
  have h := arithmeticMapWithWork_extra
    (bellmanActionReadWithWork distance L read query)
    (bellmanActionWithWork distance L (fun s => (read s).1) query)
    (fun _ => M * (R + 3)) actions
    (fun action _ => bellmanActionReadWithWork_eq distance L read query action)
    (fun action ha => bellmanActionReadWithWork_cost distance L read query action R (hread action ha))
  have hs : (actions.map (fun _ => M * (R + 3))).sum = actions.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold bellmanReadWithWork bellmanWithWork
  dsimp only
  rw [h.1]
  omega

theorem bellmanWithWork_action_count {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) :
    actions.length ≤ (bellmanWithWork distance L fallback child query actions).2 := by
  have h := arithmeticMapWithWork_length_le_cost
    (bellmanActionWithWork distance L child query) actions
  change actions.length ≤ _ + _ + 1
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source
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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The warmup continuation evaluates finite input-table lookups and
charges their scan costs at the point where each returned word is used. -/

namespace EditApproximation
namespace BinaryFraction



theorem localWarmupReadKernelWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny)
    (I C : ℕ) (hi : ∀ r, (initial r).2 ≤ I) (hc : ∀ input, (child input).2 ≤ C) :
    (localWarmupReadKernelWithWork parent N P F a initial child query).2 ≤
      (localWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).2 * (I + M * (C + 3) + 4) := by
  let reps := localRepresentativesWithWork N P F a (fun r => (initial r).1) query
  let acts := wideActionsFromRepresentativesWithWork M parent reps.1 P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := bellmanWithWork endpointDistanceWithWork L.1 (initial query).1
    (fun input => (child input).1) query acts.1
  have hr := localRepresentativeReadWithWork_eq_cost N P F a initial query I hi
  have hb := bellmanReadWithWork_cost endpointDistanceWithWork L.1 (initial query).1
    child query acts.1 C (fun action _ i => hc (action.childState i))
  have hn := bellmanWithWork_action_count endpointDistanceWithWork L.1 (initial query).1
    (fun input => (child input).1) query acts.1
  have hquery := hi query
  have hr' : (localRepresentativeReadWithWork N P F a initial query).2 ≤ reps.2 * (I + 2) := hr.2
  have hb' : (bellmanReadWithWork endpointDistanceWithWork L.1 (initial query).1
      child query acts.1).2 ≤ result.2 + acts.1.length * (M * (C + 3)) := hb
  have hn' : acts.1.length ≤ result.2 := hn
  unfold localWarmupReadKernelWithWork
  dsimp only
  rw [hr.1]
  change (initial query).2 + (localRepresentativeReadWithWork N P F a initial query).2 +
    acts.2 + L.2 + (bellmanReadWithWork endpointDistanceWithWork L.1 (initial query).1
      child query acts.1).2 + 3 ≤
    (reps.2 + acts.2 + L.2 + result.2 + 3) * (I + M * (C + 3) + 4)
  have hh := Nat.mul_le_mul_right (M * (C + 3)) hn'
  have hrFactor := Nat.mul_le_mul_left reps.2
    (show I + 2 ≤ I + M * (C + 3) + 4 by omega)
  have haFactor : acts.2 ≤ acts.2 * (I + M * (C + 3) + 4) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left acts.2
      (show 1 ≤ I + M * (C + 3) + 4 by omega)
  have hLFactor : L.2 ≤ L.2 * (I + M * (C + 3) + 4) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left L.2
      (show 1 ≤ I + M * (C + 3) + 4 by omega)
  have hresultFactor : result.2 + result.2 * (M * (C + 3)) ≤
      result.2 * (I + M * (C + 3) + 4) := by
    calc
      _ = result.2 * (1 + M * (C + 3)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hconstant : I + 3 ≤ 3 * (I + M * (C + 3) + 4) := by omega
  nlinarith only [hr', hb', hquery, hh, hrFactor, haFactor, hLFactor, hresultFactor, hconstant]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
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



theorem work_bind {ι α β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).work oracle readWork =
      program.work oracle readWork + (next (program.value oracle)).work oracle readWork := by
  induction program with
  | done result => simp only [bind, work, value, Nat.zero_add]
  | read key continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]
  | charge steps continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]

/- A local charged step executes a Boolean routine with an explicit cost. -/


theorem work_collect {ι κ β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).work oracle readWork =
      (inputs.map fun key => (reader key).work oracle readWork + 3).sum +
      (next (inputs.map fun key => (reader key).value oracle)).work oracle readWork := by
  induction inputs generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key inputs ih =>
    simp only [collect, work_bind, work, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupBuffers
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

private theorem warmup_read_sum {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (hc : ∀ key, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have h := hc key
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryWarmupProgram_work_bound_oai {ι : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F B C : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (q : TargetInterval ny) (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
    (hc : ∀ r, ((childRead r).value oracle).width ≤ B)
    (hiC : ∀ r, (initialRead r).work oracle readWork ≤ C)
    (hcC : ∀ r, (childRead r).work oracle readWork ≤ C) :
    (queryWarmupProgram parent N P F a initialRead childRead q).work oracle readWork ≤
      queryWarmupProgramBitBudget M P F B C := by
  let value := (initialRead q).value oracle
  let centers := queryRawCentersWithWork N P F a value q
  let words := centers.1.map fun r => (initialRead r).value oracle
  let initial := queryOverrideParentReadWithWork value q centers.1 words
  let inputs := queryWarmupInputsWithWork M parent N P F a initial q
  let childWords := inputs.1.map fun input => (childRead input).value oracle
  let child := fun input : Fin M × TargetInterval ny => queryChildReadWithWork inputs.1 childWords input.1 input.2
  have hcenters := queryRawCentersWithWork_bounds N P F B a value q (by omega) hN hF hFpos hP hPb
    (by omega) ha (hi q)
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
  have hiR : ∀ r, (initial r).2 ≤ queryWarmupParentReadBudget P F B := by
    intro r
    apply (queryOverrideParentReadWithWork_cost value q centers.1 words r).trans
    unfold queryWarmupParentReadBudget
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul hcenters.1 (by omega))
  have hinputs := queryWarmupInputsWithWork_bounds M N P F B _ parent hP a initial q (by omega)
    hN hF hFpos hPb (by omega) (by omega) hM ha hiW hiR
  have hcW : ∀ input, (child input).1.width ≤ B := by
    intro input
    exact gatheredWordLookupWithWork_width _ inputs.1 childWords input B (by omega) (by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hc key)
  have hcR : ∀ input, (child input).2 ≤ queryWarmupChildReadBudget M P F B := by
    intro input
    exact (queryChildReadWithWork_cost inputs.1 childWords input.1 input.2 B hM (by omega)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hinputs.1) 1)
  have hkernel := (localWarmupReadKernelWithWork_cost parent N P F a initial child q _ _ hiR hcR).trans
    (Nat.mul_le_mul_right _ (localWarmupKernelWithWork_bounds parent N P F B hP hFpos a
      (fun r => (initial r).1) (fun input => (child input).1) q hB hN hnx hny hM hPb hF ha hiW hcW).2)
  have hsumI := (warmup_read_sum centers.1 (fun r => (initialRead r).work oracle readWork + 3)
    (C + 3) (fun r => Nat.add_le_add_right (hiC r) 3)).trans (Nat.mul_le_mul_right _ hcenters.1)
  have hsumC := (warmup_read_sum inputs.1 (fun r => (childRead r).work oracle readWork + 3)
    (C + 3) (fun r => Nat.add_le_add_right (hcC r) 3)).trans (Nat.mul_le_mul_right _ hinputs.1)
  have hq := hiC q
  have hcentercost : centers.2 ≤ queryRawCentersBitBudget P F B := hcenters.2
  have hinputcost : inputs.2 ≤ queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) := hinputs.2
  simp only [queryWarmupProgram, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero]
  change (initialRead q).work oracle readWork + (centers.2 +
    ((centers.1.map fun r => (initialRead r).work oracle readWork + 3).sum +
    (inputs.2 + ((inputs.1.map fun r => (childRead r).work oracle readWork + 3).sum +
    (localWarmupReadKernelWithWork parent N P F a initial child q).2)))) ≤ _
  calc
    _ ≤ C + (queryRawCentersBitBudget P F B +
        (queryWarmupRepresentatives P F B * (C + 3) +
        (queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) +
        ((queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
        localWarmupBitBudget M P F B *
          (queryWarmupParentReadBudget P F B + M * (queryWarmupChildReadBudget M P F B + 3) + 4))))) :=
      Nat.add_le_add hq (Nat.add_le_add hcentercost
        (Nat.add_le_add hsumI (Nat.add_le_add hinputcost (Nat.add_le_add hsumC hkernel))))
    _ = _ := by unfold queryWarmupProgramBitBudget; omega

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.queryWarmupProgram_work_bound_oai.{u_1} := @OAI.EditApproximation.queryWarmupProgram_work_bound_oai.{u_1}
