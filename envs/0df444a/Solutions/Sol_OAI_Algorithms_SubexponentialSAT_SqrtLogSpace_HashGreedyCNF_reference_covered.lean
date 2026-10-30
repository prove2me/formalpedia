-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.reference_covered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:09:38.179836+00:00
-- url     : https://prove2.me/submissions/59e1cad8-d3b2-4105-b3d2-49a2f5d10a13

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

theorem encodeDigits_mem {m depth : ℕ} (width : ℕ) (a : Fin depth → Fin (3 * m)) :
    encodeDigits width a ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth := by
  apply List.mem_map.mpr
  refine ⟨(List.ofFn fun j => fixedBits width (a j).val).flatten, ?_, rfl⟩
  have h := powerRows_contains (alphabet m width)
    (List.ofFn fun j => fixedBits width (a j).val) [[]] [] (by simp) ?_
  · simpa using h
  · intro word hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact List.mem_map.mpr ⟨(a j).val, List.mem_range.mpr (a j).isLt, rfl⟩

theorem encode_mem {m depth : ℕ} (width : ℕ) (h : Candidate m depth) :
    encode width h ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth :=
  encodeDigits_mem width _

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

theorem powerRows_decompose (alphabet rows : List (List Bool)) (depth : ℕ)
    (bits : List Bool) (hbits : bits ∈ powerRows alphabet depth rows) :
    ∃ front ∈ rows, ∃ words : List (List Bool),
      words.length = depth ∧ (∀ word ∈ words, word ∈ alphabet) ∧
      bits = front ++ words.flatten := by
  induction depth generalizing rows with
  | zero => exact ⟨bits, hbits, [], rfl, by simp, by simp⟩
  | succ depth ih =>
      obtain ⟨mid, hmid, words, hlen, hw, heq⟩ :=
        ih (cartesianOutput rows alphabet) hbits
      simp only [cartesianOutput, List.mem_reverse, List.mem_flatMap] at hmid
      obtain ⟨front, hp, hmid⟩ := hmid
      obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hmid
      refine ⟨front, hp, word :: words, by simp [hlen], ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hword
        · exact hw a ha
      · simpa [List.flatten_cons, List.append_assoc] using heq

theorem readChunks_uniform (width : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) :
    readChunks width words.length words.flatten = words.map BinaryArithmetic.toNat := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      have hword := hw word (by simp)
      have hwords : ∀ a ∈ words, a.length = width := by
        intro a ha
        exact hw a (by simp [ha])
      have ht (tail : List Bool) : (word ++ tail).take width = word := by
        exact List.take_left' hword
      have hd (tail : List Bool) : (word ++ tail).drop width = tail := by
        exact List.drop_left' hword
      simp only [List.length_cons, List.flatten_cons, List.map_cons, readChunks, ht, hd]
      rw [ih hwords]

theorem generated_chunks_valid {m width depth : ℕ}
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    ∀ v ∈ readChunks width depth payload.reverse, v < 3 * m := by
  obtain ⟨bits, hbits, rfl⟩ := List.mem_map.mp hp
  obtain ⟨front, hfront, words, hlen, hwords, heq⟩ :=
    powerRows_decompose (alphabet m width) [[]] depth bits hbits
  have hpref : front = [] := by simpa using hfront
  subst front
  simp only [List.nil_append] at heq
  subst bits
  rw [List.reverse_reverse, ← hlen, readChunks_uniform width words
    (fun a ha => alphabet_width m width a (hwords a ha))]
  intro v hv
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hwords word hword)
  have hi' := List.mem_range.mp hi
  rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ (hi'.trans_le hw)]
  exact hi'

theorem generated_payload_width (m width depth : ℕ) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    payload.length = depth * width :=
  HashSelectProgram.generatedPayloads_width _ _ _ (alphabet_width m width) _ hp

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

theorem payload_covers_word {m depth : ℕ} (bits : List Bool)
    (hb : bits.length = payloadWidth m depth) :
    ∃ i, payload m depth i = bits := by
  have hv : CounterPrograms.value bits.reverse < 2 ^ payloadWidth m depth := by
    simpa only [List.length_reverse, hb] using ExecCNFTupleOdometer.value_lt_power_length bits.reverse
  refine ⟨⟨CounterPrograms.value bits.reverse, hv⟩, ?_⟩
  apply List.reverse_injective
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [hb]
  · simp

theorem digitWidth_sufficient (m : ℕ) : 3 * m ≤ 2 ^ digitWidth m :=
  (DyadicWidth.lt_two_pow_width _).le

theorem encode_length {m depth : ℕ} (h : Candidate m depth) :
    (HashFamilyPayload.encode (digitWidth m) h).length = payloadWidth m depth :=
  HashFamilyPayload.generated_payload_width _ _ _ _
    (HashFamilyPayload.encode_mem _ h)

theorem chunks_shape {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).map List.length = List.replicate depth (digitWidth m) := by
  apply List.map_splitLengths_length
  simp [hraw, payloadWidth]

theorem chunks_width {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    ∀ word ∈ chunks m depth raw, word.length = digitWidth m := by
  intro word hw
  have hmem : word.length ∈ (chunks m depth raw).map List.length :=
    List.mem_map.mpr ⟨word, hw, rfl⟩
  rw [chunks_shape hraw] at hmem
  exact (List.mem_replicate.mp hmem).2

theorem chunks_flatten {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).flatten = raw.reverse := by
  apply List.flatten_splitLengths
  simp [hraw, payloadWidth]

theorem normalize_valid {m depth : ℕ} (raw : List Bool)
    (hr : raw ∈ HashSelectProgram.generatedPayloads
      (HashFamilyPayload.alphabet m (digitWidth m)) depth) : normalize m depth raw = raw := by
  have hraw : raw.length = payloadWidth m depth :=
    HashFamilyPayload.generated_payload_width _ _ _ _ hr
  have hread : HashFamilyPayload.readChunks (digitWidth m) depth raw.reverse =
      (chunks m depth raw).map BinaryArithmetic.toNat := by
    have h := HashFamilyPayload.readChunks_uniform (digitWidth m) (chunks m depth raw)
      (chunks_width hraw)
    simpa [chunks_flatten hraw] using h
  have hmap : (chunks m depth raw).map (fun word =>
      SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))) =
        chunks m depth raw := by
    conv_rhs => rw [← List.map_id (chunks m depth raw)]
    apply List.map_congr_left
    intro word hw
    have hmem : BinaryArithmetic.toNat word ∈
        HashFamilyPayload.readChunks (digitWidth m) depth raw.reverse := by
      rw [hread]
      exact List.mem_map.mpr ⟨word, hw, rfl⟩
    have hv := HashFamilyPayload.generated_chunks_valid (digitWidth_sufficient m) raw hr _ hmem
    apply ExecCNFTupleEnumeration.word_eq_of_length_value
    · simp [chunks_width hraw word hw]
    · rw [CounterPrograms.value_eq_toNat, CounterPrograms.value_eq_toNat,
        Nat.mod_eq_of_lt hv, SubexpLiftRing.toNat_fixedBits_of_lt _ _
          (hv.trans_le (digitWidth_sufficient m))]
      rfl
  simp [normalize, hmap, chunks_flatten hraw]

theorem normalized_covers_candidate {m depth : ℕ}
    (h : Candidate m depth) :
    ∃ i, normalize m depth (payload m depth i) = HashFamilyPayload.encode (digitWidth m) h := by
  obtain ⟨i, hi⟩ := payload_covers_word
    (HashFamilyPayload.encode (digitWidth m) h) (encode_length h)
  refine ⟨i, ?_⟩
  rw [hi]
  exact normalize_valid _ (HashFamilyPayload.encode_mem _ h)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
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

theorem candidate_covers {m depth : ℕ} (h : HashFamily.Candidate m depth) :
    ∃ rank < 2 ^ HashCandidates.payloadWidth m depth,
      candidate m depth rank = HashFamilyPayload.encode (HashCandidates.digitWidth m) h := by
  obtain ⟨i, hi⟩ := HashCandidates.normalized_covers_candidate h
  exact ⟨i.val, i.isLt, hi⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete streamed selector uses the original ternary row semantics.
Its exact scores and normalized reference coverage discharge the greedy
contraction hypotheses. These statements concern the deterministic history
refined by the native run; native query and resource closure remain separate. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

theorem reference_covered_oai {n m depth c : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hcount : (3 * m) ^ depth = c + 1) (rows : List (List Bool)) (i : Fin (c + 1)) :
    ∃ rank < 2 ^ HashCandidates.payloadWidth m depth,
      (entry clauses depth rows rank).payload = reference hcount i :=
  HashGreedyCandidate.candidate_covers _

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.reference_covered_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.reference_covered_oai
