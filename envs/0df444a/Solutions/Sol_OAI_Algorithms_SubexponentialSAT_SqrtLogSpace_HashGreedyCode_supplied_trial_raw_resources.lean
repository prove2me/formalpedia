-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:14:29.359131+00:00
-- url     : https://prove2.me/submissions/6c9737ee-010a-4097-a6f6-7b8356febd4f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_history_raw_rows
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_history_raw_slots

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

theorem iter_length (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (initial : List (List Bool)) (q : ℕ) :
    (HashSelectProgram.iter (nextRows entry C) q initial).length = initial.length + q := by
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    simp [nextRows, ih, Nat.add_assoc]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashScopeProgram

theorem slots_le {α : Type*} (rows : List (List α)) (D : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ D) : slots rows ≤ rows.length * D := by
  induction rows with
  | nil => simp [slots]
  | cons row rows ih =>
    have hr := h row (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [slots, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem supplied_slots {m B : ℕ} (s : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    slots (CodeRowsProgram.serializedRows m s Q) ≤
      SparseCode.totalRows m B * SparseCode.degreeBound m B := by
  simpa [CodeRowsProgram.serializedRows_supplied_length] using
    slots_le (CodeRowsProgram.serializedRows m s Q) (SparseCode.degreeBound m B)
      (CodeRowsProgram.serializedRows_supplied_slots s Q)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

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

theorem rawDecode_length (m width : ℕ) (hm : 0 < m) (payload : List Bool) :
    (rawDecode m width hm payload).length = payload.length / width := by
  simp [rawDecode, HashInputProgram.candidateTerms]

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

theorem rawDecode_generated_length {m width depth : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (payload : List Bool) (hp : payload ∈ generatedPayloads (HashFamilyPayload.alphabet m width) depth) :
    (rawDecode m width hm payload).length = depth := by
  rw [rawDecode_length, HashFamilyPayload.generated_payload_width m width depth payload hp,
    Nat.mul_div_cancel _ (HashFamilyPayload.width_pos hm hw)]

theorem initialPayloads_decode {m width : ℕ} (hm : 0 < m) (hw : 3*m ≤ 2^width)
    (rows : List (List (Fin m × ZMod 3))) :
    (initialPayloads width rows).map (rawDecode m width hm) = rows := by
  simp [initialPayloads, List.map_map, Function.comp_def, rawDecode_rowPayload hm hw]

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

theorem initial_raw {m B : ℕ} (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) :
    (initial shifts Q).map (raw m hm) = CodeRowsProgram.serializedRows m shifts Q :=
  LeafScopeResourceBounds.initialPayloads_decode hm (HashCandidates.digitWidth_sufficient m) _

/-- A normalized candidate always decodes to exactly depth raw occurrences. -/
theorem candidate_raw_length {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (raw m hm (HashGreedyCandidate.candidate m depth rank)).length = depth :=
  LeafScopeResourceBounds.rawDecode_generated_length hm (HashCandidates.digitWidth_sufficient m)
    _ (HashGreedyCandidate.candidate_mem hm depth rank)

/-- All trials, including losers, have bounded physical raw-row resources. -/
theorem supplied_trial_raw_resources_oai {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (rounds rank : ℕ) :
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    rows.length = SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots rows ≤
        SparseCode.totalRows m B * SparseCode.degreeBound m B +
          (rounds + 1) * SparseCode.distanceDenom m B ∧
      ∀ row ∈ rows, row.length ≤ SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1 := by
  dsimp only
  have hi : ∀ bits ∈ initial shifts Q, (raw m hm bits).length ≤ SparseCode.degreeBound m B := by
    intro bits hb
    apply CodeRowsProgram.serializedRows_supplied_slots shifts Q
    rw [← initial_raw hm shifts Q]
    exact List.mem_map.mpr ⟨bits, hb, rfl⟩
  have hlen : (initial shifts Q).length = SparseCode.totalRows m B := by
    simp [initial, LeafScopeResourceBounds.initialPayloads,
      CodeRowsProgram.serializedRows_supplied_length]
  refine ⟨?_, ?_, ?_⟩
  · simp [history, HashGreedyRound.iter_length, hlen, Nat.add_assoc]
  · have hh := history_raw_slots clauses hm (SparseCode.distanceDenom m B) (initial shifts Q) rounds
    rw [initial_raw hm shifts Q] at hh
    have hs := LeafScopeResourceBounds.supplied_slots shifts Q
    simp only [List.map_cons, LeafScopeResourceBounds.slots, List.sum_cons]
    simp only [LeafScopeResourceBounds.slots] at hh
    rw [candidate_raw_length, hh]
    nlinarith
  · intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · rw [candidate_raw_length]
      omega
    · exact history_raw_rows clauses hm _ _ _ hi rounds row hrow

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources_oai
