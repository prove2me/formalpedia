-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:12:01.768818+00:00
-- url     : https://prove2.me/submissions/c1afd2ba-9b34-4696-bfe0-676e21ed38a7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramGenerate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-depth tuple enumeration by the audited 83-label finite controller.
The selector reads the generator's existing framed queue directly: reversing
payload interpretation accounts for the parser's stack order without a free
array conversion. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

theorem cartesian_width (alphabet rows : Records) (a b : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) (hb : ∀ x ∈ rows, x.length = b) :
    ∀ x ∈ TupleProgram.cartesianOutput rows alphabet, x.length = b + a := by
  intro x hx
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap] at hx
  obtain ⟨row, hr, hx⟩ := hx
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hx
  simp [ha word hw, hb row hr]

theorem powerRows_width (alphabet rows : Records) (a b depth : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) (hb : ∀ x ∈ rows, x.length = b) :
    ∀ x ∈ TupleProgram.powerRows alphabet depth rows, x.length = b + depth * a := by
  induction depth generalizing rows b with
  | zero => simpa [TupleProgram.powerRows] using hb
  | succ depth ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (b + a)
      (cartesian_width alphabet rows a b ha hb)
    simpa [TupleProgram.powerRows, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

theorem generatedPayloads_width (alphabet : Records) (a depth : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) :
    ∀ x ∈ generatedPayloads alphabet depth, x.length = depth * a := by
  intro x hx
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hx
  have h := powerRows_width alphabet [[]] a 0 depth ha (by simp) word hw
  simpa using h

end SubexponentialSAT.SqrtLog.HashSelectProgram

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

theorem alphabet_width (m width : ℕ) :
    ∀ a ∈ alphabet m width, a.length = width := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp

theorem cartesian_mem {alphabet rows : List (List Bool)} {front word : List Bool}
    (hp : front ∈ rows) (hw : word ∈ alphabet) :
    front ++ word ∈ cartesianOutput rows alphabet := by
  simp only [cartesianOutput, List.mem_reverse, List.mem_flatMap]
  exact ⟨front, hp, List.mem_map.mpr ⟨word, hw, rfl⟩⟩

/-- Internal reversals of the generator's list order do not affect coverage. -/
theorem powerRows_contains (alphabet words rows : List (List Bool)) (front : List Bool)
    (hp : front ∈ rows) (hw : ∀ a ∈ words, a ∈ alphabet) :
    front ++ words.flatten ∈ powerRows alphabet words.length rows := by
  induction words generalizing rows front with
  | nil => simpa [powerRows] using hp
  | cons word words ih =>
      have hword : word ∈ alphabet := hw word (by simp)
      have hwords : ∀ a ∈ words, a ∈ alphabet := by
        intro a ha
        exact hw a (by simp [ha])
      have h := ih (cartesianOutput rows alphabet) (front ++ word)
        (cartesian_mem hp hword) hwords
      simpa [powerRows, List.flatten_cons, List.append_assoc] using h

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadValid
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

theorem generated_payload_width (m width depth : ℕ) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    payload.length = depth * width :=
  HashSelectProgram.generatedPayloads_width _ _ _ (alphabet_width m width) _ hp

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

/-- The actual normalizer emits the original valid candidate encoding family,
so the old native row assembler can be reused with its original hypotheses. -/
theorem normalize_mem {m : ℕ} (hm : 0 < m) (depth : ℕ) (raw : List Bool) :
    normalize m depth raw ∈
      HashSelectProgram.generatedPayloads (HashFamilyPayload.alphabet m (digitWidth m)) depth := by
  let words := (chunks m depth raw).map fun word =>
    SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))
  apply List.mem_map.mpr
  refine ⟨words.flatten, ?_, rfl⟩
  have hwords : ∀ word ∈ words, word ∈ HashFamilyPayload.alphabet m (digitWidth m) := by
    intro word hw
    obtain ⟨chunk, _, rfl⟩ := List.mem_map.mp hw
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩
  have h := HashFamilyPayload.powerRows_contains
    (HashFamilyPayload.alphabet m (digitWidth m)) words [[]] [] (by simp) hwords
  simpa [words] using h


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
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

theorem candidate_mem {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    candidate m depth rank ∈ HashSelectProgram.generatedPayloads
      (HashFamilyPayload.alphabet m (HashCandidates.digitWidth m)) depth :=
  HashCandidates.normalize_mem hm depth _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single raw-slot decoder for the actual logical records returned by the
selector's parser. It retains zero-coefficient and repeated entries. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

theorem rawDecode_length (m width : ℕ) (hm : 0 < m) (payload : List Bool) :
    (rawDecode m width hm payload).length = payload.length / width := by
  simp [rawDecode, HashInputProgram.candidateTerms]

theorem rawDecode_generated_length {m width depth : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (payload : List Bool) (hp : payload ∈ generatedPayloads (HashFamilyPayload.alphabet m width) depth) :
    (rawDecode m width hm payload).length = depth := by
  rw [rawDecode_length, HashFamilyPayload.generated_payload_width m width depth payload hp,
    Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- A normalized candidate always decodes to exactly depth raw occurrences. -/
theorem candidate_raw_length {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (raw m hm (HashGreedyCandidate.candidate m depth rank)).length = depth :=
  LeafScopeResourceBounds.rawDecode_generated_length hm (HashCandidates.digitWidth_sufficient m)
    _ (HashGreedyCandidate.candidate_mem hm depth rank)

theorem chosen_raw_length {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (rows : List (List Bool)) :
    (raw m hm (HashGreedyRound.chosenEntry (entry clauses depth)
      (HashCandidates.payloadWidth m depth) rows).payload).length = depth := by
  obtain ⟨rank, _, he⟩ := HashGreedyRound.chosenEntry_mem (entry clauses depth)
    (HashCandidates.payloadWidth m depth) rows
  rw [he]
  exact candidate_raw_length hm depth rank

theorem history_raw_rows_oai {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth D : ℕ) (start : List (List Bool))
    (hstart : ∀ bits ∈ start, (raw m hm bits).length ≤ D) (rounds : ℕ) :
    ∀ row ∈ (history clauses depth start rounds).map (raw m hm), row.length ≤ D + depth + 1 := by
  induction rounds with
  | zero =>
    intro row hrow
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hrow
    have h := hstart bits hb
    exact h.trans (by omega)
  | succ rounds ih =>
    intro row hrow
    unfold history at hrow
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows, List.map_cons] at hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · rw [chosen_raw_length clauses hm]
      omega
    · exact ih row hrow

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_rows_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_rows_oai
