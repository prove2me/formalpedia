-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:33:15.234181+00:00
-- url     : https://prove2.me/submissions/2b23873e-a1cf-4164-82b3-91a4a58af411

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Serialization_uniform_guarded_lengths_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_query_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryEntry_prepared_accepted_entry
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_frontend_budget
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_numeric_caps
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_accepted
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_common_bounds

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SparsificationBudgetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A directly computed dyadic sparsification budget

For each fixed width k, a fixed control constant T suffices.  The selected
parameter is a power of two whose binary length is an affine function of the
binary length of the inverse budget.  This is the explicit witness from
SparsificationBudget.dyadic_witness, rather than the least passing candidate.

The control constant is chosen before the input word.  Program definitions
below manipulate bits only; their specifications use the corresponding
natural-number values.
-/

namespace SubexponentialSAT.SparsificationBudgetProgram

open SubexponentialSAT.CounterPrograms

/-! ## The actual fixed finite program -/

theorem bits_length_le (s : ℕ) : s.bits.length ≤ s := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_pow_self (by decide))

/-! ## The input-size to inverse-budget to M pipeline -/

end SubexponentialSAT.SparsificationBudgetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An executable finite argmin. Scores are natural numbers, not unary
word lengths. The companion trace records both score calls at every scan
step, including repeated calls and all losing candidates. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

variable {R : Type*}

theorem best_mem (score : R → ℕ) (seed : R) (rs : List R) :
    best score seed rs ∈ seed :: rs := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    by_cases hs : score r < score seed
    · simp only [hs, ↓reduceIte]
      exact List.mem_cons_of_mem seed (ih r)
    · simp only [hs, ↓reduceIte]
      rcases List.mem_cons.mp (ih seed) with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The streamed strict argmin and its greedy invariant. Candidate indices describe
an iterator's successive callbacks; no list of candidates is constructed here.
The finite-program implementation must refine these recurrences. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy

open OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect
open scoped BigOperators

variable {R X : Type*}


private theorem best_append (evaluate : R → ℕ) (seed : R) (xs ys : List R) :
    best evaluate seed (xs ++ ys) = best evaluate (best evaluate seed xs) ys := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- The native iterator's proof-only visit log agrees with the indexed scan.
The seed's repeated visit at index zero leaves its cached score unchanged. -/
theorem scan_eq_best (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).1 =
      best evaluate (candidate 0) ((List.range' 0 (t + 1)).map candidate) := by
  induction t with
  | zero => simp [scan, best]
  | succ t ih =>
    rw [List.range'_concat, List.map_append, best_append]
    simp only [Nat.one_mul, Nat.zero_add, List.map_cons, List.map_nil, best, ← ih]
    simp only [scan, update, scan_score]
    split_ifs <;> rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem iter_succ_apply {α : Type*} (next : α → α) (n : ℕ) (x : α) :
    iter next (n + 1) x = next (iter next n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [iter] using ih (next x)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete streamed greedy rounds. The query seam below consists of actual
executions of the fixed attempt command; it must be instantiated by the native
exact-query implementation before an endpoint theorem can use these results. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem chosenEntry_eq_best (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    chosenEntry entry C rows = HashSelect.best BinaryArgmin.value (entry rows 0)
      ((List.range' 0 (2 ^ C)).map (entry rows)) := by
  have hp : 1 ≤ 2 ^ C := by have := pow_pos (by decide : 0 < (2 : ℕ)) C; omega
  simpa only [chosenEntry, Nat.sub_add_cancel hp] using
    HashGreedy.scan_eq_best BinaryArgmin.value (entry rows) (2 ^ C - 1)

theorem chosenEntry_mem (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    ∃ j < 2 ^ C, chosenEntry entry C rows = entry rows j := by
  have hm := HashSelect.best_mem BinaryArgmin.value (entry rows 0)
    ((List.range' 0 (2 ^ C)).map (entry rows))
  rw [← chosenEntry_eq_best] at hm
  rcases List.mem_cons.mp hm with hzero | hrest
  · exact ⟨0, pow_pos (by decide) _, hzero⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hrest
    exact ⟨j, by simpa using hj, he.symm⟩

theorem chosenEntry_fits (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (B C : ℕ) (rows : List (List Bool))
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    BinaryArgmin.Fits B C (chosenEntry entry C rows) := by
  obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
  rw [he]
  exact hfit j hj

theorem iter_length (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (initial : List (List Bool)) (q : ℕ) :
    (HashSelectProgram.iter (nextRows entry C) q initial).length = initial.length + q := by
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    simp [nextRows, ih, Nat.add_assoc]

/-- The physical serialized history grows only by the selected bounded row.
The exponentially many losing payloads never contribute to this retained word. -/
theorem encodedHistory_iter_length_le
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (B C count : ℕ)
    (initial : List (List Bool))
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    ∀ q ≤ count,
      (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length ≤
        (encodedHistory initial).length + q * (2 * C + 2) := by
  intro q
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    intro hq
    have hi := ih (by omega)
    have hfitChosen := chosenEntry_fits entry B C
      (HashSelectProgram.iter (nextRows entry C) q initial)
      (hfit _ (by rw [iter_length]; omega))
    have hbytes := hfitChosen.2
    rw [HashSelectProgram.iter_succ_apply]
    have hlen : (encodedHistory (nextRows entry C
        (HashSelectProgram.iter (nextRows entry C) q initial))).length =
        (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length +
          2 * (chosenEntry entry C (HashSelectProgram.iter (nextRows entry C) q initial)).payload.length + 2 := by
      simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
      omega
    rw [hlen, Nat.succ_mul q (2 * C + 2)]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem entry_fits {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ) :
    BinaryArgmin.Fits (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)
      (entry rowAccept weight n m depth rows rank) := by
  constructor <;> simp [entry]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

theorem finalStaged_sources (a : Data) :
    (finalStaged a).stacks 700=a.stacks 784 ∧
    (finalStaged a).stacks 701=a.stacks 777 ∧
    (finalStaged a).stacks 707=a.stacks 782 ∧
    (finalStaged a).stacks 708=a.stacks 783 ∧
    (finalStaged a).stacks 709=a.stacks 785 := by
  simp [finalStaged,masterRoutes,routesState,routed]

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

theorem temporary_frame (a : State 40 896) (i : Fin 896) (hi : i ≠ 767) :
    (temporaryCleared a).stacks i = a.stacks i := clearStacks_frame _ _ _ hi

theorem staged_sources (a : State 40 896) :
    (staged a).stacks 700 = a.stacks 784 ∧
    (staged a).stacks 701 = a.stacks 777 ∧
    (staged a).stacks 707 = a.stacks 782 ∧
    (staged a).stacks 708 = a.stacks 783 ∧
    (staged a).stacks 709 = a.stacks 785 := by
  simpa only [staged, temporary_frame _ 784 (by decide), temporary_frame _ 777 (by decide),
    temporary_frame _ 782 (by decide), temporary_frame _ 783 (by decide),
    temporary_frame _ 785 (by decide)] using LeafOuterNative.finalStaged_sources (temporaryCleared a)

theorem staged_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (staged a).stacks i = a.stacks i := by
  have hn : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [HashMassStaged.stagedPorts] using hi
  exact (LeafOuterNative.finalStaged_frame _ i hn.1 hn.2.1
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).trans (temporary_frame a i ht)

/-- The accepted history stage does not use the trial-prefix scratch. -/
theorem staged_702 (a : State 40 896) : (staged a).stacks 702 = a.stacks 702 :=
  (LeafOuterNative.finalStaged_frame _ 702 (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans (temporary_frame a 702 (by decide))

theorem staged_temporary (a : State 40 896) : (staged a).stacks 767 = [] := by
  change (LeafOuterNative.finalStaged (temporaryCleared a)).stacks 767 = []
  rw [LeafOuterNative.finalStaged_frame _ 767 (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp [temporaryCleared]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF HashGreedyCode

theorem history_bytes {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    (encodedHistory (history clauses depth start rounds)).length ≤
      (encodedHistory start).length + rounds * (2 * HashCandidates.payloadWidth m depth + 2) := by
  exact HashGreedyRound.encodedHistory_iter_length_le (entry clauses depth)
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) rounds start
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) rounds le_rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryShadow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The literal staged collector entry has a uniformly bounded proof shadow.
Only the five caller words left unrestricted by the query-time binder are
erased. No executable instruction, query evaluation, or semantic answer is
assumed in these physical input bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay
open HashMassAdapter HashGreedyExecution

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

/-- History-only staging copies visible master words and physically clears
its temporary. It needs no bound on remaining caller counters. -/
theorem accepted_staged_visible_bound (a : State 40 896) (L : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∀ i, ¬ H i → ((AcceptedQueryStage.staged a).stacks i).length ≤ L := by
  intro i hi
  have h := AcceptedQueryStage.staged_sources a
  by_cases h0 : i = 700
  · subst i; rw [h.1]; exact ha 784 (by decide)
  by_cases h1 : i = 701
  · subst i; rw [h.2.1]; exact ha 777 (by decide)
  by_cases h7 : i = 707
  · subst i; rw [h.2.2.1]; exact ha 782 (by decide)
  by_cases h8 : i = 708
  · subst i; rw [h.2.2.2.1]; exact ha 783 (by decide)
  by_cases h9 : i = 709
  · subst i; rw [h.2.2.2.2]; exact ha 785 (by decide)
  by_cases h702 : i = 702
  · subst i; rw [AcceptedQueryStage.staged_702]; exact ha 702 (by decide)
  by_cases h767 : i = 767
  · subst i; rw [AcceptedQueryStage.staged_temporary]; simp
  rw [AcceptedQueryStage.staged_frame a i (by
    simpa [HashMassStaged.stagedPorts] using
      (show i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 from
        ⟨h0,h1,h702,h7,h8,h9⟩)) h767]
  exact ha i hi

/-- The actual final RowBoundary suffices for the accepted entry shadow.
Its remaining-round word781 is unrestricted and erased, while the physical
history byte cap is retained. -/
theorem accepted_shadow_bound (base selected : State 40 896) (rows : List (List Bool)) (L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hboundary : HashGreedyRound.RowBoundary base rows selected)
    (hhistory : (HashGreedyProgram.encodedHistory rows).length ≤ L) :
    ∀ i, ((rebaseState H (fun _ => []) (AcceptedQueryStage.staged selected)).stacks i).length ≤ L := by
  apply CommandStackTransport.shadow_stack_bound
  apply accepted_staged_visible_bound
  intro i hi
  by_cases h777 : i = 777
  · subst i
    simpa only [hboundary.history] using hhistory
  have h781 : i ≠ 781 := by
    intro he; subst i; exact hi (by decide)
  rw [hboundary.frame i h777 h781]
  exact hbase i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafScopeInputBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem conversionCost_mono {a b : ℕ} (h : a ≤ b) : conversionCost a ≤ conversionCost b := by
  unfold conversionCost
  gcongr

theorem numericCost_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.numericCost k ≤ numericMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hk := (SparsificationBudgetProgram.bits_length_le k).trans h.widthParameter
  have hf := conversionCost_mono h.free
  have ho := conversionCost_mono h.occurrence
  have ha := conversionCost_mono h.arity
  have hq := conversionCost_mono h.factors
  have hm := conversionCost_mono h.incidences
  have hn := h.ambientBits
  have hc := h.modulus
  unfold Query.numericCost numericCost numericMajorant
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendMajorants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT LeafParametersProgram.FrontendBounds

theorem parameterSize_poly : Poly (fun S : ℕ => S+1) parameterSize := by
  refine ⟨parameterSize 1,4,?_⟩
  intro S
  have hp (i : ℕ) (hi : i ≤ 4) : S^i ≤ (S+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  unfold parameterSize numericMajorant conversionCost
  nlinarith only [h0,h1,h2,h3,h4]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafScopeInputBounds
open LeafParametersProgram.FrontendBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem parameter_counts_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    CountsBound (q.input k) (parameterSize (capacity q k)) := by
  have h := query_bounds q k hv
  have h0 := h.ambient
  have h1 := h.free
  have h2 := h.clauseCount
  have h3 := h.occurrence
  have h4 := h.arity
  have h5 := h.factors
  have h6 := h.widthParameter
  have h7 := h.incidences
  have hm := hv.2.2.2.2.2.1
  intro i
  fin_cases i
  · change BinaryArithmetic.toNat q.ambient ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).free ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change BinaryArithmetic.toNat q.modulus ≤ parameterSize (capacity q k)
    rw [hm]
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).occurrence ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change completedArity q.scopeRows q.forward ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change q.scopeRows.length+(totals q.scopeRows q.forward).uncovered ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change k ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).incidences ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega

theorem parameter_lengths_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    ∀ i, q.inputLengths k i ≤ parameterSize (capacity q k) := by
  intro i
  have h := numericCost_bound q k hv
  change q.numericCost k ≤ _
  unfold parameterSize
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

/-- Visible words retain their complete bit strings. -/
theorem visible (a : Data) (i : Fin 896) (hi : i ∉ HighQueryProgram.Carried.words) :
    (erase a).stacks i = a.stacks i :=
  rebaseStacks_of_not_mem (fun j => j ∈ HighQueryProgram.Carried.words)
    (fun _ => []) a.stacks i hi

/-- Erasure preserves an existing blank, whether or not the word is carried. -/
theorem blank (a : Data) (i : Fin 896) (hi : a.stacks i = []) :
    (erase a).stacks i = [] := by
  by_cases hm : i ∈ HighQueryProgram.Carried.words
  · exact rebaseStacks_of_mem (fun j => j ∈ HighQueryProgram.Carried.words)
      (fun _ => []) a.stacks i hm
  · exact (visible a i hm).trans hi

/-- The actual lower-bank clean-work predicate needs only its existing blanks. -/
theorem cleanWork (a : Data)
    (hc : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)) :
    LeafProgram.Query.CleanWork (HighMarkedFrontend.project (erase a)) := by
  intro i hi h321
  exact blank a (HighMarkedFrontend.stackMap i) (hc i hi h321)

/-- All five immutable frontend source fields are visible to the shadow. -/
theorem sources (q : LeafQueryFrontend.Query) (a : Data)
    (hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)) :
    LeafProgram.Query.Sources q (HighMarkedFrontend.project (erase a)) := by
  constructor
  · exact (visible a 700 (by decide)).trans hs.formula
  · exact (visible a 701 (by decide)).trans hs.rows
  · exact (visible a 707 (by decide)).trans hs.modulus
  · exact (visible a 708 (by decide)).trans hs.width
  · exact (visible a 709 (by decide)).trans hs.ambient

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem ready_low {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] :=
  NativeCodeAssembly.worker_empty a hr.worker

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry LeafParametersProgram CostAssembly.Polynomial
open NativeQueryPreparation ProducedQueryResources

/-- Canonical padding comes from the real frontend inputLengths definition;
the checked FrontState.canonicalLengths identifies these same words later. -/
theorem canonical_lengths_cubic : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k T : ℕ), q.Valid →
      LeafScopeInputBounds.capacity q k ≤ 106 * T ^ 3 →
      ∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ C * (T + 1) ^ d := by
  obtain ⟨C,d,h⟩ := Serialization.uniform_guarded_lengths_polynomial
  have hp : Ordinary (fun T => C *
      (LeafQueryFrontend.parameterSize (106 * T ^ 3) + 1) ^ d) := by
    obtain ⟨A,e,hA⟩ := LeafQueryFrontend.parameterSize_poly
    have hinner : Ordinary (fun T => A * (106 * T ^ 3 + 1) ^ e) :=
      ordinary_mul (ordinary_const A) (ordinary_pow
        (ordinary_add (ordinary_mul (ordinary_const 106) (ordinary_pow ordinary_id 3))
          (ordinary_const 1)) e)
    obtain ⟨D,f,hD⟩ := ordinary_mul (ordinary_const C)
      (ordinary_pow (ordinary_add hinner (ordinary_const 1)) d)
    refine ⟨D,f,?_⟩
    intro T
    exact (Nat.mul_le_mul_left C (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hA (106*T^3)) 1) d)).trans (hD T)
  obtain ⟨A,e,hA⟩ := hp
  refine ⟨A,e,?_⟩
  intro q k T hv hcap i
  have hcounts := LeafQueryFrontend.parameter_counts_bound q k hv
  have hlengths := LeafQueryFrontend.parameter_lengths_bound q k hv
  have hmono : LeafQueryFrontend.parameterSize (LeafScopeInputBounds.capacity q k) ≤
      LeafQueryFrontend.parameterSize (106*T^3) := by
    unfold LeafQueryFrontend.parameterSize LeafQueryFrontend.numericMajorant LeafQueryFrontend.conversionCost
    gcongr
  exact (h (q.input k) (q.inputLengths k) _ hcounts hlengths i).trans
    ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hmono 1) d)).trans (hA T))

/-- The common physical selector cap dominates its own scalar sum. -/
theorem scalar_le_common (n m B W : ℕ) :
    HashQueryInputBounds.commonCap n m B W ≤ NativeLeafRun.commonBound n m B W := by
  have h := Nat.le_self_pow (show 3 ≠ 0 by decide)
    (HashQueryInputBounds.commonCap n m B W)
  unfold NativeLeafRun.commonBound
  omega

/-- The history-only final query uses the same kind of concrete source cap;
there is no candidate product and no unrestricted caller-word contribution. -/
theorem accepted_inputs (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : State 40 896,
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ R) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      q.Valid ∧ ambient q = n ∧ 1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      (∀ j, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧ 3*L+2 ≤ S := by
  obtain ⟨Cn,dn,cutoff,hnum⟩ := HashQueryParameterBounds.accepted_numeric_caps k hk
  obtain ⟨Cl,dl,hlen⟩ := canonical_lengths_cubic
  obtain ⟨Cf,df,hfront⟩ := HashQueryParameterBounds.accepted_frontend_budget
  refine ⟨Cn,dn,Cl,dl,Cf,df,max cutoff 1,?_⟩
  intro n N R hcut hinput B F hv hm hmb shifts Q rounds hr d hmasters
    hformula hhistory hwidth hmod hamb hclean q L S
  have hn : 0 < n := by omega
  obtain ⟨hvq,hqn,_hscan,_hsmall,hnumpos,hnnum,hinum,hvalues⟩ :=
    hnum n N (by omega) hinput F hv hm hmb shifts Q rounds hr d hwidth hmod hamb
  obtain ⟨hcapacity,hcost⟩ := hfront n k B R F hn hm shifts Q rounds hr d
    hmasters hformula hhistory hwidth hmod hamb hclean
  have hscalar := scalar_le_common n F.length B R
  have hbase : HashQueryInputBounds.commonCap n F.length B R+k+1 ≤ L+k+1 := by
    dsimp only [L]
    omega
  have hnS : Cn*(N+1)^dn ≤ S := by dsimp only [S,sourceCap]; omega
  have hlS : Cl*(L+k+1)^dl ≤ S := by dsimp only [S,sourceCap]; omega
  have hfrontcost : q.inputBudget k ≤ Cf*(L+k+1)^df :=
    hcost.trans (Nat.mul_le_mul_left Cf (Nat.pow_le_pow_left hbase df))
  refine ⟨hvq,hqn,hnumpos.trans hnS,hnnum.trans hnS,hinum.trans hnS,?_,?_,?_,?_⟩
  · intro padding j
    exact ⟨(hvalues padding j).1.trans hnS,(hvalues padding j).2.trans hnS⟩
  · intro j
    exact (hlen q k _ hvq hcapacity j).trans
      ((Nat.mul_le_mul_left Cl (Nat.pow_le_pow_left hbase dl)).trans hlS)
  · change q.inputBudget k+5 ≤ frontendCap Cf df L k
    unfold frontendCap
    omega
  · dsimp only [S,sourceCap]
    omega


/-- Actual Setup uses a smaller frontend cost than the uniform literal-query
allowance, so its retained local bound fits the same preparedCap. -/
theorem setup_local_bound_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
      (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp) ≤
        preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
  dsimp only [HighQuerySetup.localBound, preparedCap]
  gcongr

/-- The actual source-prefix bound is a maximum with the carried frame;
its local polynomial has no hidden-word or repeated-node scratch term. -/
theorem setup_prefix_bound_le (q : LeafQueryFrontend.Query)
    (Cp dp Cn dn Cl dl Cf df N L k f B : ℕ)
    (hf : f ≤ frontendCap Cf df L k) (hn : BinaryArithmetic.toNat q.ambient ≤ N) :
    HighQuerySetup.prefixBound q (sourceCap Cn dn Cl dl N L k+f)
      (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp) B ≤
        max (12*preparedCap Cp dp Cn dn Cl dl Cf df N L k+4*N+6) B := by
  have hp := setup_local_bound_le Cp dp Cn dn Cl dl Cf df N L k f hf
  unfold HighQuerySetup.prefixBound HighQuerySetup.boundaryBound
  omega

/-- The measured frontend/preparation/seed cost uses the same actual
local bound; it never uses the collector's physical length. -/
theorem setup_time_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    f + Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp +
      110*HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
        (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp)+81 ≤
      frontendCap Cf df L k+111*preparedCap Cp dp Cn dn Cl dl Cf df N L k+81 := by
  have hp := setup_local_bound_le Cp dp Cn dn Cl dl Cf df N L k f hf
  have hc : Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
    have h := Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left
      (show sourceCap Cn dn Cl dl N L k+f+1 ≤
        sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+1 by omega) dp)
    dsimp only [preparedCap,HighQuerySetup.localBound]
    omega
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual prepared selector boundary supplies the literal marked and
history-only frontend, packing, arithmetic and high-counter initialization.
The common bound is unchanged. Suspended caller words have a separate bound
which never occurs in the measured setup time. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

private theorem shadow_visible (a : Data) (L : ℕ)
    (h : ∀ i, ((ProgramTapeReplay.rebaseState
      (fun i : Fin 896 => i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
      (fun _ => []) a).stacks i).length ≤ L) :
    ∀ i, ¬ H i → (a.stacks i).length ≤ L := by
  intro i hi
  have hn : ¬(i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781) := by
    simpa only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] using hi
  simpa only [ProgramTapeReplay.rebaseState,
    ProgramTapeReplay.rebaseStacks_of_not_mem
      (fun i : Fin 896 => i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
      (fun _ => []) a.stacks i hn] using h i

/-- These are precisely the immutable physical facts needed by the numeric
input bounds, recovered from preparation and the actual six-port frame. -/
private theorem boundary_facts {n B R : ℕ} (F : RawCNF n)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (base d : Data)
    (hr : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hb : ∀ i, (base.stacks i).length ≤ R)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hamb : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i) :
    (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ R) ∧
    d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
    (d.stacks 783).length = HashCandidates.digitWidth F.length ∧
    BinaryArithmetic.toNat (d.stacks 782) = F.length ∧
    BinaryArithmetic.toNat (d.stacks 785) = n ∧
    LeafProgram.Query.CleanWork (project d) ∧ d.stacks 767 = [] := by
  have hm (i : Fin 896) (hi : 782 ≤ i.val) : d.stacks i = base.stacks i := by
    apply hf i <;> intro he <;> subst i <;> contradiction
  have hlo (i : Fin 896) (hi : i.val < 768) : d.stacks i = [] := by
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro he; subst j; omega
    rw [hf i (hn 770 (by decide)) (hn 771 (by decide)) (hn 777 (by decide))
      (hn 778 (by decide)) (hn 779 (by decide)) (hn 781 (by decide))]
    exact NativeLeafRun.ready_low hr i hi
  refine ⟨?_, (hm 784 (by decide)).trans hformula, ?_, ?_, ?_, ?_, hlo 767 (by decide)⟩
  · intro i hi
    rw [hm i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide)]
    exact hb i
  · rw [hm 783 (by decide), hr.width]; exact hr.modulus_length
  · rw [hm 782 (by decide)]; exact hr.clauses
  · rw [hm 785 (by decide)]; exact hamb
  · intro i _ _; exact hlo (stackMap i) i.isLt

/-- The final history-only input constructs the same real setup without a
trial candidate or marked clause, at the unchanged prepared common bound. -/
theorem accepted_with_shadow_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : Data) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      AcceptedEntry q input ∧ ambient q = n ∧
      q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project input)) (HighMarkedFrontend.acceptedBudget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
      Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project (HighQueryEntryShadow.erase input)))
        (HighMarkedFrontend.acceptedBudget q k) S 0 Cp dp
        (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  obtain ⟨Cp,dp,hsetup⟩ := HighQuerySetup.accepted
  obtain ⟨Cn,dn,Cl,dl,Cf,df,cutoff₁,hinputs⟩ := accepted_inputs k hk
  obtain ⟨_Cg,_dg,cutoff₂,hguard⟩ := HashQueryParameterBounds.accepted_numeric_caps k hk
  refine ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,max (max cutoff₁ cutoff₂) 1,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr base d hidden
    hreadyBase hbase hformula hamb hboundary input hhidden q L S P
  have hn : 0 < n := by omega
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i :=
    fun i _ _ h777 _ _ h781 => hboundary.frame i h777 h781
  obtain ⟨hmasters,hformula',hwidth,hmod,hamb',hclean,_hscratch⟩ :=
    boundary_facts F shifts Q base d hreadyBase hbase hformula hamb hframe
  have hentry := prepared_accepted_entry F hn hm shifts Q rounds base d
    hreadyBase hformula hamb hboundary
  obtain ⟨_hvq,hqn,hS,hnS,hiS,hval,hlen,hfront,h3L⟩ := hinputs n N R (by omega) hN F hv hm hmb
    shifts Q rounds hr d hmasters hformula' hboundary.history hwidth hmod hamb' hclean
  obtain ⟨_,_,hscan,_⟩ := hguard n N (by omega) hN F hv hm hmb shifts Q rounds hr d hwidth hmod hamb'
  obtain ⟨hRL,_hround,_hC,_hcounterBound,hbytes,_href,_hgrowth,_hnL⟩ :=
    NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
  have hhistoryBound : (HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)).length ≤ L :=
    (HashQueryInputBounds.history_bytes (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _).trans hbytes)
  have hshadow := HashQueryShadow.accepted_shadow_bound base d _ L
    (fun i => (hbase i).trans hRL) hboundary hhistoryBound
  change 3*L+2 ≤ S at h3L
  have hvisible : ∀ i, ¬ H i → (input.stacks i).length ≤ S :=
    fun i hi => (shadow_visible input L hshadow i hi).trans (by omega)
  obtain ⟨nf,front,padding,w,hfe,hft,hfs,run,he,ht,hkept,hspace⟩ :=
    hsetup q k hscan.guard input S hidden hentry.valid hentry.clean hentry.sources hentry.unmarked
      hentry.index hvisible hhidden (fun j => (hval _ j).1) hlen
  have hzvisible : ∀ i, ¬ H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ S := by
    intro i hi
    rw [HighQueryEntryShadow.visible input i hi]
    exact hvisible i hi
  have hzhidden : ∀ i, H i → ((HighQueryEntryShadow.erase input).stacks i).length ≤ 0 := by
    intro i hi
    simp [HighQueryEntryShadow.erase, ProgramTapeReplay.rebaseState,
      ProgramTapeReplay.rebaseStacks, hi]
  obtain ⟨nz,frontz,paddingz,wz,hfez,hftz,hfsz,runz,hez,htz,hkeptz,hspacez⟩ :=
    hsetup q k hscan.guard (HighQueryEntryShadow.erase input) S 0 hentry.valid
      (HighQueryEntryShadow.cleanWork input hentry.clean)
      (HighQueryEntryShadow.sources q input hentry.sources) hentry.unmarked hentry.index
      hzvisible hzhidden (fun j => (hval _ j).1) hlen
  refine ⟨hentry,hqn,?_,hS,hnS,hiS,hval,hfront,
    ⟨⟨⟨hscan.guard, nf, front, padding, w, run⟩, {
      input_visible := hvisible
      frontend := hfe
      frontend_time := hft
      frontend_state := hfs
      eval := he
      time := ?_
      kept := hkept
      space := ?_ }⟩⟩,
    ⟨⟨⟨hscan.guard, nz, frontz, paddingz, wz, runz⟩, {
      input_visible := hzvisible
      frontend := hfez
      frontend_time := hftz
      frontend_state := hfsz
      eval := hez
      time := ?_
      kept := hkeptz
      space := ?_ }⟩⟩⟩
  · simp [q, acceptedQuery, rawQueryFromRows, rawQuery, recordMark,
      LeafProgram.PreparedSource.markIndex, Encoding.encodeNat]
  · exact ht.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz hz i => (hspace.bound t z htz hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ hidden hfront (hqn.trans_le hN))⟩
  · exact htz.trans (setup_time_le Cp dp Cn dn Cl dl Cf df N L k _ hfront)
  · exact ⟨fun t z htz' hz i => (hspacez.bound t z htz' hz i).trans
      (setup_prefix_bound_le q Cp dp Cn dn Cl dl Cf df N L k _ 0 hfront (hqn.trans_le hN))⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow_oai
