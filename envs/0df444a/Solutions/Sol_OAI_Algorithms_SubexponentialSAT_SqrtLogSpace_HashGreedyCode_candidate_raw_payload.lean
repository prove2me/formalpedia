-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:10:09.095826+00:00
-- url     : https://prove2.me/submissions/bccc272c-78da-49be-abe3-972b39cecd83

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAlphabetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Canonical scalar alphabet by an actual binary countdown

At each positive counter value the program copies and decrements the copy,
then prepends its fixed-width word as a record. The controller decrements the
original counter afterward. Thus descending visits produce ascending records.
-/

namespace SubexponentialSAT.SubexpAlphabetProgram

open BitProgram StructuredCalls CounterPrograms Subexp.TupleProgram

theorem canonical_word (word : List Bool) :
    word = SubexpLiftRing.fixedBits word.length (value word) := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact (SubexpLiftRing.fixedBits_length _ _).symm
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt]
    · exact (value_eq_toNat word).symm
    · simpa only [value_eq_toNat] using ModularArithmetic.toNat_lt_pow_length word

end SubexponentialSAT.SubexpAlphabetProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadRoundTrip
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

theorem ofFn_getD_values (values : List ℕ) (depth : ℕ) (hlen : values.length = depth) :
    List.ofFn (fun j : Fin depth => values.getD j.val 0) = values := by
  subst depth
  have hf : (fun j : Fin values.length => values.getD j.val 0) = values.get := by
    funext j
    exact List.getD_eq_getElem values 0 j.isLt
  rw [hf, List.ofFn_get]

theorem fixedBits_toNat (word : List Bool) :
    fixedBits word.length (BinaryArithmetic.toNat word) = word := by
  simpa only [CounterPrograms.value_eq_toNat] using
    (SubexpAlphabetProgram.canonical_word word).symm

theorem generated_reconstruct {m width depth : ℕ} (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    (((readChunks width depth payload.reverse).map (fixedBits width)).flatten).reverse =
      payload := by
  obtain ⟨bits, hbits, rfl⟩ := List.mem_map.mp hp
  obtain ⟨front, hfront, words, hlen, hwords, heq⟩ :=
    powerRows_decompose (alphabet m width) [[]] depth bits hbits
  have hf : front = [] := by simpa using hfront
  subst front
  simp only [List.nil_append] at heq
  subst bits
  rw [List.reverse_reverse, ← hlen, readChunks_uniform width words
    (fun a ha => alphabet_width m width a (hwords a ha))]
  have hm : (words.map BinaryArithmetic.toNat).map (fixedBits width) = words := by
    rw [List.map_map]
    calc
      words.map (fixedBits width ∘ BinaryArithmetic.toNat) = words.map id := by
        apply List.map_congr_left
        intro word hword
        have hw := alphabet_width m width word (hwords word hword)
        simpa only [Function.comp_apply, id_eq, hw] using fixedBits_toNat word
      _ = words := List.map_id words
  rw [hm]

/-- Every actual generated record has exactly the canonical encoding of its
decoded candidate. This is stronger than equality of the induced row. -/
theorem encode_decode_generated {m depth width : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    encode width (decode m depth width hm payload) = payload := by
  let values := readChunks width depth payload.reverse
  have hlen : values.length = depth := readChunks_length width depth payload.reverse
  have hvalid : ∀ v ∈ values, v < 3 * m := generated_chunks_valid hw payload hp
  have hget (j : Fin depth) : values.getD j.val 0 < 3 * m := by
    have hj : j.val < values.length := by simpa only [hlen] using j.isLt
    apply hvalid
    rw [List.getD_eq_getElem values 0 hj]
    exact List.get_mem values ⟨j.val, hj⟩
  have hlist : List.ofFn (fun j : Fin depth => values.getD j.val 0 % (3 * m)) = values := by
    have hf : (fun j : Fin depth => values.getD j.val 0 % (3 * m)) =
        (fun j : Fin depth => values.getD j.val 0) := by
      funext j
      exact Nat.mod_eq_of_lt (hget j)
    rw [hf]
    exact ofFn_getD_values values depth hlen
  change encodeDigits width ((candidateDigitsEquiv m depth)
    ((candidateDigitsEquiv m depth).symm (fun j =>
      ⟨values.getD j.val 0 % (3 * m), Nat.mod_lt _ (by omega)⟩))) = payload
  rw [Equiv.apply_symm_apply]
  unfold encodeDigits
  have hmap :
      List.ofFn (fun j : Fin depth => fixedBits width (values.getD j.val 0 % (3 * m))) =
        values.map (fixedBits width) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (fixedBits width)) hlist
  change (List.ofFn (fun j : Fin depth =>
    fixedBits width (values.getD j.val 0 % (3 * m)))).flatten.reverse = payload
  rw [hmap]
  exact generated_reconstruct payload hp

end SubexponentialSAT.SqrtLog.HashFamilyPayload

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

/-- Exact physical payload recovery for every generated candidate. -/
theorem rawDecode_generated_payload {m width depth : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (payload : List Bool) (hp : payload ∈ generatedPayloads (HashFamilyPayload.alphabet m width) depth) :
    (CodeRowsProgram.rowPayload width m (rawDecode m width hm payload)).reverse = payload := by
  have hlen : payload.length / width = depth := by
    rw [HashFamilyPayload.generated_payload_width m width depth payload hp,
      Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]
  change HashInputProgram.Loop.rawInput width (rawDecode m width hm payload) = payload
  unfold rawDecode
  rw [hlen, HashInputProgram.candidate_rawInput]
  exact HashFamilyPayload.encode_decode_generated hm hw payload hp

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

/-- Re-encoding a normalized streamed candidate recovers its literal stored
payload, including all zero and repeated raw slots. -/
theorem candidate_raw_payload_oai {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m
      (raw m hm (HashGreedyCandidate.candidate m depth rank))).reverse =
        HashGreedyCandidate.candidate m depth rank :=
  LeafScopeResourceBounds.rawDecode_generated_payload hm
    (HashCandidates.digitWidth_sufficient m) _ (HashGreedyCandidate.candidate_mem hm depth rank)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload_oai
