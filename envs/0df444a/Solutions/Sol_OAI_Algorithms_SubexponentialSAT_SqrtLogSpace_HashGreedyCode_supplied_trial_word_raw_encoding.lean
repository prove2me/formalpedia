-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:14:58.656297+00:00
-- url     : https://prove2.me/submissions/64e24e1c-1b77-422f-bde7-2ad0ed8263bf

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_candidate_raw_payload

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

theorem lt_two_pow_width (m : ℕ) : m < 2 ^ width m :=
  Nat.lt_pow_succ_log_self (by decide) m

end SubexponentialSAT.DyadicWidth

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator bit alphabet and its reverse-aware semantic
decoder. The alphabet matches `SubexpAlphabetProgram.command_eval`. -/

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

theorem readChunks_encode (width : ℕ) (xs : List ℕ)
    (hx : ∀ i ∈ xs, i < 2 ^ width) :
    readChunks width xs.length ((xs.map (fixedBits width)).flatten) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hhead := hx x (by simp)
      have htail : ∀ i ∈ xs, i < 2 ^ width := by
        intro i hi
        exact hx i (by simp [hi])
      have ht (tail : List Bool) : (fixedBits width x ++ tail).take width = fixedBits width x := by
        simp
      have hd (tail : List Bool) : (fixedBits width x ++ tail).drop width = tail := by
        simp
      simp only [List.length_cons, List.map_cons, List.flatten_cons, readChunks, ht, hd]
      rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hhead, ih htail]

theorem decode_encodeDigits {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (a : Fin depth → Fin (3 * m)) :
    decode m depth width hm (encodeDigits width a) = decodeDigits a := by
  apply congrArg decodeDigits
  funext j
  apply Fin.ext
  have hx : ∀ i ∈ List.ofFn (fun j => (a j).val), i < 2 ^ width := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact (a j).isLt.trans_le hw
  have hc := readChunks_encode width (List.ofFn fun j => (a j).val) hx
  simp only [List.length_ofFn, List.map_ofFn, Function.comp_def] at hc
  simp only [ encodeDigits, List.reverse_reverse]
  rw [hc]
  simp [Nat.mod_eq_of_lt (a j).isLt]

theorem decode_encode {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decode m depth width hm (encode width h) = h := by
  rw [encode, decode_encodeDigits hm width hw]
  exact (candidateDigitsEquiv m depth).symm_apply_apply h

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily

theorem width_pos {m width : ℕ} (hm : 0 < m) (hw : 3 * m ≤ 2 ^ width) :
    0 < width := by
  by_contra h
  have hz : width = 0 := by omega
  simp only [hz, pow_zero] at hw
  omega

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

theorem digitWidth_sufficient (m : ℕ) : 3 * m ≤ 2 ^ digitWidth m :=
  (DyadicWidth.lt_two_pow_width _).le


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- The parser reverses the current odometer word, exactly as the reference
candidate accessor does. No native decoding of the exponential rank occurs. -/
theorem payload_wordRank {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    HashCandidates.payload m depth (wordRank word hlen) = word.reverse := by
  apply congrArg List.reverse
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [hlen]
  · exact ExecCNFTupleEnumeration.fixedBits_value _ _ (wordRank word hlen).isLt

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
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

theorem candidate_at_word {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    candidate m depth (CounterPrograms.value word) = HashCandidates.normalize m depth word.reverse := by
  have h := HashCandidateRank.payload_wordRank word hlen
  simpa only [HashCandidates.payload, HashCandidateRank.wordRank, candidate] using
    congrArg (HashCandidates.normalize m depth) h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The assembler receives exactly the selector's raw candidate bytes. Its
source is a serialized original formula, and its result is a produced inline
row, with every raw tuple occurrence retained. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem candidate_rawInput {m depth : ℕ} (width : ℕ)
    (h : HashFamily.Candidate m depth) :
    Loop.rawInput width (candidateTerms h) = HashFamilyPayload.encode width h := by
  simp only [Loop.rawInput,candidateTerms,List.map_ofFn,HashFamilyPayload.encode,
    HashFamilyPayload.encodeDigits]
  rfl

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single raw-slot decoder for the actual logical records returned by the
selector's parser. It retains zero-coefficient and repeated entries. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

theorem listCandidate_terms {m : ℕ} (row : List (Fin m × ZMod 3)) :
    HashInputProgram.candidateTerms (listCandidate row) = row := by
  simp [HashInputProgram.candidateTerms, listCandidate]

theorem listCandidate_encode {m : ℕ} (width : ℕ) (row : List (Fin m × ZMod 3)) :
    HashFamilyPayload.encode width (listCandidate row) = (CodeRowsProgram.rowPayload width m row).reverse := by
  rw [← HashInputProgram.candidate_rawInput, listCandidate_terms]
  rfl

theorem rawDecode_rowPayload {m width : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (row : List (Fin m × ZMod 3)) :
    rawDecode m width hm (CodeRowsProgram.rowPayload width m row).reverse = row := by
  have hlen : (CodeRowsProgram.rowPayload width m row).reverse.length / width = row.length := by
    rw [List.length_reverse, CodeRowsProgram.rowPayload_length,
      Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]
  unfold rawDecode
  rw [hlen, ← listCandidate_encode, HashFamilyPayload.decode_encode hm width hw,
    listCandidate_terms]

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual supplied-code row payloads initialize_ the streamed selector. Raw
slot bounds retain repeated indices and zero coefficients, as the physical
assembler does; they do not substitute semantic support for retained data. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

/-- Every actual selected history payload has an exact raw-row decoding.
Selection membership comes from the concrete streamed minimum proof. -/
theorem supplied_history_raw_payloads {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
    ∀ p ∈ history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds,
      (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p)).reverse = p := by
  induction rounds with
  | zero =>
    intro p hp
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hp
    unfold raw
    rw [LeafScopeResourceBounds.rawDecode_rowPayload hm (HashCandidates.digitWidth_sufficient m)]
  | succ rounds ih =>
    intro p hp
    unfold history at hp
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨rank, _, he⟩ := HashGreedyRound.chosenEntry_mem
        (entry clauses (SparseCode.distanceDenom m B))
        (HashCandidates.payloadWidth m (SparseCode.distanceDenom m B))
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)
      unfold history at he
      rw [he]
      exact candidate_raw_payload hm _ rank
    · exact ih p hp

/-- This is byte equality between the existing history stream and the raw
scope-stage input. It does not perform an uncharged reversal or conversion. -/
theorem raw_encoding {m : ℕ} (hm : 0 < m) (rows : List (List Bool))
    (hrows : ∀ p ∈ rows,
      (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p)).reverse = p) :
    HashGreedyProgram.encodedHistory rows =
      HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m) (rows.map (raw m hm)) := by
  unfold HashGreedyProgram.encodedHistory HashScopeProgram.RawTable.inputBits
  apply congrArg (Encoding.encodeList id)
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have h := congrArg List.reverse (hrows p hp)
  have hbits : HashScopeProgram.RawTable.rowBits (HashCandidates.digitWidth m) (raw m hm p) =
      CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p) := rfl
  rw [Function.comp_apply, hbits]
  simpa only [List.reverse_reverse] using h.symm

/-- The actual staged candidate prefix and777 tail equal the literal raw
trial table for every rank, including losing candidates. -/
theorem supplied_trial_raw_encoding {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds rank : ℕ) :
    true :: (Encoding.frame (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank).reverse ++
      HashGreedyProgram.encodedHistory
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) := by
  have h := raw_encoding hm
    (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds) (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact candidate_raw_payload hm _ rank
        · exact supplied_history_raw_payloads clauses hm shifts Q rounds p hp)
  simpa only [HashGreedyProgram.encodedHistory, List.map_cons, Encoding.encodeList, id_eq]
    using h

/-- The binary odometer's actual current word selects exactly the same raw
trial table; leading zero bits and the parser's reversal are accounted for. -/
theorem supplied_trial_word_raw_encoding_oai {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (rounds : ℕ) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m (SparseCode.distanceDenom m B)) :
    true :: (Encoding.frame
      (HashCandidates.normalize m (SparseCode.distanceDenom m B) word.reverse).reverse ++
      HashGreedyProgram.encodedHistory
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) (CounterPrograms.value word) ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) := by
  rw [← HashGreedyCandidate.candidate_at_word word hword]
  exact supplied_trial_raw_encoding clauses hm shifts Q rounds _

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding_oai
