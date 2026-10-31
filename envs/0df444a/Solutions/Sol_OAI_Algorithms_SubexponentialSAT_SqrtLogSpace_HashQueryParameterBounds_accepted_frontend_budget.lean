-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:05:23.45923+00:00
-- url     : https://prove2.me/submissions/44d9de84-a2c5-4e4a-a831-728419d28aaa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_inputBudget_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryEntry_accepted_entry

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

theorem encodedHistory_length_le (rows : List (List Bool)) (C : ℕ)
    (hC : ∀ bits ∈ rows, bits.length ≤ C) :
    (encodedHistory rows).length ≤ rows.length * (2 * C + 2) + 1 := by
  induction rows with
  | nil => simp [encodedHistory, Encoding.encodeList]
  | cons bits rows ih =>
    have hb := hC bits (by simp)
    have hr := ih (fun word hw => hC word (by simp [hw]))
    simp only [encodedHistory, List.map_cons, Encoding.encodeList, id_eq,
      List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse] at *
    nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le_bound (m B : ℕ) : degree m B ≤ degreeBound m B := min_le_right _ _

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem slots_length (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (slots m shifts Q side v a).length ≤ D := by
  exact (List.length_filterMap_le _ _).trans_eq List.length_finRange

theorem rowPayload_length (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) :
    (rowPayload b m ss).length=ss.length*b := by
  induction ss with
  | nil => simp [rowPayload]
  | cons s ss ih =>
    change ((SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)) ++ rowPayload b m ss).length = _
    simp only [List.length_append,SubexpLiftRing.fixedBits_length,ih,List.length_cons]
    simp [Nat.add_mul,Nat.add_comm]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The precise order emitted by the native vertex/check loops. Each row is
present even when shortening removes every one of its local ports. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem chronologicalRows_length (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    (chronologicalRows m shifts Q).length=2^r*(2*t) := by
  simp [chronologicalRows,List.length_flatMap,List.sum_replicate,Nat.mul_comm
    ]
  omega

theorem serializedRows_length (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    (serializedRows m shifts Q).length=2^r*(2*t) := by
  simpa [serializedRows] using chronologicalRows_length (m:=m) shifts Q

theorem mem_serializedRows_iff (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (ss : List (Fin m × SparseCode.F3)) :
    ss∈serializedRows m shifts Q ↔
      ∃ side v a, slots m shifts Q side v a=ss := by
  simp only [serializedRows,List.mem_reverse,chronologicalRows,List.mem_flatMap,
    List.mem_finRange,true_and,List.mem_append,List.mem_ofFn]
  constructor
  · rintro ⟨i,⟨a,h⟩|⟨a,h⟩⟩
    · exact ⟨false,WalshExistence.cubeEquiv r i,a,h⟩
    · exact ⟨true,WalshExistence.cubeEquiv r i,a,h⟩
  · rintro ⟨side,v,a,h⟩
    refine ⟨(WalshExistence.cubeEquiv r).symm v,?_⟩
    cases side
    · exact Or.inl ⟨a,by simpa using h⟩
    · exact Or.inr ⟨a,by simpa using h⟩

theorem serializedRows_slots_bound (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (ss : List (Fin m × SparseCode.F3)) (h : ss∈serializedRows m shifts Q) :
    ss.length ≤ D := by
  obtain ⟨side,v,a,rfl⟩ := (mem_serializedRows_iff shifts Q ss).mp h
  exact slots_length shifts Q side v a

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSupplied
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SparseCode

theorem serializedRows_supplied_length {m B : ℕ}
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) :
    (serializedRows m s Q).length=totalRows m B := by
  simpa [totalRows, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (serializedRows_length (m := m) s Q)

theorem serializedRows_supplied_slots {m B : ℕ}
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (row : List (Fin m × F3)) (hrow : row∈serializedRows m s Q) :
    row.length ≤ degreeBound m B :=
  (serializedRows_slots_bound s Q row hrow).trans (degree_le_bound m B)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- The original serializer retains all slots, including repeats and zeros. -/
theorem initial_bytes {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    (encodedHistory (initial shifts Q)).length ≤ SparseCode.totalRows m B *
      (2 * (SparseCode.degreeBound m B * HashCandidates.digitWidth m) + 2) + 1 := by
  have h := encodedHistory_length_le (initial shifts Q)
    (SparseCode.degreeBound m B * HashCandidates.digitWidth m) (by
      intro bits hb
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
      rw [List.length_reverse, CodeRowsProgram.rowPayload_length]
      exact Nat.mul_le_mul_right _ (CodeRowsProgram.serializedRows_supplied_slots shifts Q row hr))
  simpa only [HashGreedyCode.initial, LeafScopeResourceBounds.initialPayloads, List.length_map,
    CodeRowsProgram.serializedRows_supplied_length] using h

theorem history_bytes {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    (encodedHistory (history clauses depth start rounds)).length ≤
      (encodedHistory start).length + rounds * (2 * HashCandidates.payloadWidth m depth + 2) := by
  exact HashGreedyRound.encodedHistory_iter_length_le (entry clauses depth)
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) rounds start
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) rounds le_rfl

/-- A common cap on actual scalar parameters gives one fixed cube for all
initial, attained, and trial history streams. The index rank is unrestricted. -/
theorem serialized_bounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hrows : SparseCode.totalRows m B ≤ S)
    (hdegree : SparseCode.degreeBound m B ≤ S) (hdepth : SparseCode.distanceDenom m B ≤ S)
    (hwidth : HashCandidates.digitWidth m ≤ S) (hrounds : HashSelect.loopCap n m ≤ S)
    (rounds rank : ℕ) (hq : rounds ≤ HashSelect.loopCap n m) :
    (encodedHistory (initial shifts Q)).length ≤ 5 * S ^ 3 ∧
      (encodedHistory (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)).length
        ≤ 9 * S ^ 3 ∧
      (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank).length ≤ S ^ 2 ∧
      (encodedHistory (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)).length ≤ 16 * S ^ 3 := by
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have hDW : SparseCode.degreeBound m B * HashCandidates.digitWidth m ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hdegree hwidth
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have hi := initial_bytes shifts Q
  have hi' : (encodedHistory (initial shifts Q)).length ≤ 5 * S ^ 3 := by
    have hp := Nat.mul_le_mul hrows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hDW) 2)
    nlinarith only [hi, hp, hS3, h13]
  have hh := history_bytes clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds
  have hh' : (encodedHistory (history clauses (SparseCode.distanceDenom m B)
      (initial shifts Q) rounds)).length ≤ 9 * S ^ 3 := by
    have hp := Nat.mul_le_mul (hq.trans hrounds) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC) 2)
    nlinarith only [hh, hi', hp, hS3]
  refine ⟨hi', hh', ?_, ?_⟩
  · simpa only [HashGreedyCandidate.candidate_length] using hC
  · rw [trial_bytes, HashGreedyCandidate.candidate_length]
    nlinarith only [hh', hC, h23, h13]

theorem commonCap_bounds (n m B wordBound : ℕ) :
    1 ≤ commonCap n m B wordBound ∧ SparseCode.totalRows m B ≤ commonCap n m B wordBound ∧
      SparseCode.degreeBound m B ≤ commonCap n m B wordBound ∧
      SparseCode.distanceDenom m B ≤ commonCap n m B wordBound ∧
      HashCandidates.digitWidth m ≤ commonCap n m B wordBound ∧
      HashSelect.loopCap n m ≤ commonCap n m B wordBound ∧ wordBound ≤ commonCap n m B wordBound := by
  unfold commonCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem unmarkedInput_index (a : Data) (h705 : a.stacks 705=[]) :
    (unmarkedInput a).stacks 705=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705]

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryFrontendBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds from the actual six frontend source words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog in
/-- Physical query words, including arbitrary padding and the actual raw trial
rows, bound the capacity used by the native frontend. This is the same six
port calculation as the original query-width lemma, without its final-resource
constructor import. -/
theorem query_capacity_of_sources (q : LeafQueryFrontend.Query) (k W : ℕ)
    (a : LeafQueryFrontend.Data) (hr : q.Ready a)
    (hw : ∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
      (a.stacks i).length ≤ W) :
    LeafScopeInputBounds.capacity q k ≤
      6 * W + BinaryArithmetic.toNat q.ambient + k + 8 := by
  have h0 := hw 700 (by decide)
  have h1 := hw 701 (by decide)
  have h2 := hw 705 (by decide)
  have h3 := hw 707 (by decide)
  have h4 := hw 708 (by decide)
  have h5 := hw 709 (by decide)
  rw [hr.1] at h0
  rw [hr.2.1] at h1
  rw [hr.2.2.1] at h2
  rw [hr.2.2.2.2.1] at h3
  rw [hr.2.2.2.2.2.1] at h4
  rw [hr.2.2.2.2.2.2.1] at h5
  unfold LeafScopeInputBounds.capacity
  omega

open SqrtLog in
/-- The complete native frontend has a fixed polynomial in the actual query
word cap and ambient size. Numeric correctness alone is not used to bound
padding, raw rows, or any other retained word. -/
theorem query_frontend_sources_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (k W : ℕ)
      (a : LeafQueryFrontend.Data), q.Valid → q.Ready a →
      (∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
        (a.stacks i).length ≤ W) →
      q.inputBudget k ≤ C * (W + BinaryArithmetic.toNat q.ambient + k + 1) ^ degree := by
  obtain ⟨C, degree, hfront⟩ := LeafQueryFrontend.inputBudget_polynomial
  refine ⟨C * 9 ^ degree, degree, ?_⟩
  intro q k W a hvalid hready hwords
  have hcap := query_capacity_of_sources q k W a hready hwords
  have hsize : LeafScopeInputBounds.capacity q k + 1 ≤
      9 * (W + BinaryArithmetic.toNat q.ambient + k + 1) := by omega
  calc
    _ ≤ C * (9 * (W + BinaryArithmetic.toNat q.ambient + k + 1)) ^ degree :=
      (hfront q k hvalid).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree))
    _ = _ := by rw [mul_pow]; ring



open SqrtLog in
/-- The concrete cubic source cap supplied by the staged hash query remains a
fixed polynomial through the complete physical frontend. The constants precede
all actual queries, marks, source padding and caller states. -/
theorem query_frontend_cubic_sources_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (k S : ℕ)
      (a : LeafQueryFrontend.Data), q.Valid → q.Ready a →
      BinaryArithmetic.toNat q.ambient ≤ S → k ≤ S →
      (∀ i ∈ ([700, 701, 705, 707, 708, 709] : List (Fin 768)),
        (a.stacks i).length ≤ 16 * S ^ 3) →
      q.inputBudget k ≤ C * (S + 1) ^ degree := by
  obtain ⟨C, degree, h⟩ := query_frontend_sources_polynomial
  refine ⟨C * 19 ^ degree, 3 * degree, ?_⟩
  intro q k S a hv hr hn hk hw
  have hS : S ≤ (S + 1) ^ 3 := (Nat.le_succ S).trans (by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1 ≤ S + 1 by omega) (show 1 ≤ 3 by decide)))
  have h0 : 1 ≤ (S + 1) ^ 3 := Nat.one_le_pow' _ S
  have hp : S ^ 3 ≤ (S + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ S) 3
  have hb : 16 * S ^ 3 + BinaryArithmetic.toNat q.ambient + k + 1 ≤
      19 * (S + 1) ^ 3 := by omega
  calc
    _ ≤ C * (19 * (S + 1) ^ 3) ^ degree :=
      (h q k (16 * S ^ 3) a hv hr hw).trans
        (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb degree))
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual trial and accepted queries inherit the width-fixed scalar caps.
Every generic validity and raw-scope premise is discharged from the literal
formula, produced code rows, attained history and physical master words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry ProducedQueryResources


/-- The final unmarked frontend receives only the attained history. Its
capacity and running-time envelope use actual source bytes, never query time. -/
theorem accepted_frontend_budget_oai :
    ∃ C degree : ℕ, ∀ (n k B wordBound : ℕ) (F : RawCNF n)
      (_hn : 0 < n) (hm : 0 < F.length)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
      (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : State 40 896,
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
      LeafScopeInputBounds.capacity (acceptedQuery F hm shifts Q rounds d) k ≤
          106 * (HashQueryInputBounds.commonCap n F.length B wordBound + k) ^ 3 ∧
        (acceptedQuery F hm shifts Q rounds d).inputBudget k ≤
          C * (HashQueryInputBounds.commonCap n F.length B wordBound + k + 1) ^ degree := by
  obtain ⟨C, degree, hcost⟩ := query_frontend_cubic_sources_polynomial
  refine ⟨C, degree, ?_⟩
  intro n k B wordBound F hn hm shifts Q rounds hr d hmasters hformula hhistory
    hwidth hmod hamb hclean
  let S := HashQueryInputBounds.commonCap n F.length B wordBound + k
  have hS : 1 ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hnS : n ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hkS : k ≤ S := by unfold S; omega
  have hwS : wordBound ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  let input := AcceptedQueryStage.staged d
  let q := acceptedQuery F hm shifts Q rounds d
  have he := accepted_entry F hn hm shifts Q rounds d hformula hhistory hwidth hmod hamb hclean
  have hsources := AcceptedQueryStage.staged_sources d
  obtain ⟨hT, hrows, hdegree, hdepth, hwidth', hrounds, _hw⟩ :=
    HashQueryInputBounds.commonCap_bounds n F.length B wordBound
  have hhistoryBound := (HashQueryInputBounds.serialized_bounds (NativeLeafSemantics.indexed F)
    shifts Q _ hT hrows hdegree hdepth hwidth' hrounds rounds 0 hr).2.1
  have hhistoryBound' : (d.stacks 777).length ≤ 16 * S ^ 3 := by
    rw [hhistory]
    have hp : (HashQueryInputBounds.commonCap n F.length B wordBound) ^ 3 ≤ S ^ 3 :=
      Nat.pow_le_pow_left (by unfold S; omega) 3
    omega
  have hw : ∀ i ∈ ([700,701,705,707,708,709] : List (Fin 768)),
      ((LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project input)).stacks i).length ≤ 16 * S ^ 3 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [LeafProgram.Query.unmarkedInput_frame _ 700 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 700).length ≤ 16 * S ^ 3
      rw [hsources.1]
      have h := hmasters 784 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 701 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 701).length ≤ 16 * S ^ 3
      rw [hsources.2.1]
      exact hhistoryBound'
    · rw [LeafProgram.Query.unmarkedInput_index _ he.index_empty]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 707 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 707).length ≤ 16 * S ^ 3
      rw [hsources.2.2.1]
      have h := hmasters 782 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 708 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 708).length ≤ 16 * S ^ 3
      rw [hsources.2.2.2.1]
      have h := hmasters 783 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 709 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 709).length ≤ 16 * S ^ 3
      rw [hsources.2.2.2.2]
      have h := hmasters 785 (by decide)
      omega
  have hnq : BinaryArithmetic.toNat q.ambient = n := hamb
  have hcapacity := query_capacity_of_sources q k (16 * S ^ 3)
    (LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project input)) he.frontend hw
  rw [hnq] at hcapacity
  refine ⟨by change LeafScopeInputBounds.capacity q k ≤ 106 * S ^ 3; omega, ?_⟩
  exact hcost q k S _ he.valid he.frontend (by rw [hnq]; exact hnS) hkS hw


open CostAssembly MulticolorTypes

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget_oai
