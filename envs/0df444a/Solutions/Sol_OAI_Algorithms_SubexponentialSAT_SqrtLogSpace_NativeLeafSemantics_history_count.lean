-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:22:36.637604+00:00
-- url     : https://prove2.me/submissions/0703f354-6e76-4c12-bb57-6057e7d44d16

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_serializedRows_kernel_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCNF_history_mass_zero

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

theorem mass_eq_zero_iff [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) :
    mass rowAccept weight rows = 0 ↔
      ∀ x, accepts rowAccept rows x = true → weight x = 0 := by
  simp only [mass, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h x hx
    simpa [hx] using h x
  · intro h x
    cases hx : accepts rowAccept rows x <;> simp [hx, h x]

theorem accepts_of_forall (rowAccept : R → X → Bool) (rows : List R)
    (x : X) (h : ∀ r ∈ rows, rowAccept r x = true) :
    accepts rowAccept rows x = true := by
  exact List.all_eq_true.mpr h

theorem mass_zero_accepts_iff [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R)
    (hz : mass rowAccept weight rows = 0)
    (hs : ∀ x, weight x = 0 → ∀ r ∈ rows, rowAccept r x = true) :
    ∀ x, accepts rowAccept rows x = true ↔ weight x = 0 := by
  intro x
  constructor
  · exact (mass_eq_zero_iff rowAccept weight rows).mp hz x
  · intro hx
    exact accepts_of_forall rowAccept rows x (hs x hx)

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

theorem decodeRow_encode {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decodeRow m depth width (encode width h) = row h := by
  simp [decodeRow, hm, decode_encode hm width hw]

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

theorem generated_payload_width (m width depth : ℕ) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    payload.length = depth * width :=
  HashSelectProgram.generatedPayloads_width _ _ _ (alphabet_width m width) _ hp

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

section Hash
variable [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
omit [DecidableEq V] in
theorem violationWeight_eq_zero_iff (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x = 0 ↔ ∀ e, (C e).eval x = true := by
  simp [violationWeight, Finset.sum_eq_zero_iff]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem violationVector_of_satisfied (C : E → SAT.Clause V) (x : SAT.Assignment V)
    (hx : ∀ e, (C e).eval x = true) : violationVector (R := R) C x = 0 := by
  funext e
  simp [violationVector, clauseValue, hx e]

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectSAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiation of the finite selector with actual clause violations.
This is a conditional composition theorem: exact evaluation and initial
coverage are explicit hypotheses, not an assumed SAT oracle. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

theorem cnfRowAccept_of_zero {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (x : SAT.Assignment (Fin n)) (hx : HashInput.violationWeight C x = 0)
    (r : Row m) : cnfRowAccept C r x = true := by
  have hs := (HashInput.violationWeight_eq_zero_iff C x).mp hx
  have hv := HashInput.violationVector_of_satisfied (R := ZMod 3) C x hs
  simp [cnfRowAccept, hv]

theorem cnf_mass_zero_iff {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (rows : List (Row m)) (hzero : mass (cnfRowAccept C) (HashInput.violationWeight C) rows = 0) :
    ∀ x, accepts (cnfRowAccept C) rows x = true ↔ ∀ e, (C e).eval x = true := by
  intro x
  rw [← HashInput.violationWeight_eq_zero_iff C x]
  apply mass_zero_accepts_iff (cnfRowAccept C) (HashInput.violationWeight C) rows hzero
  intro y hy r _
  exact cnfRowAccept_of_zero C y hy r

end SubexponentialSAT.SqrtLog.HashSelect

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

theorem decodeVariableRow_generated {m width depth : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    decodeVariableRow m width payload = decodeRow m depth width payload := by
  unfold decodeVariableRow
  rw [generated_payload_width m width depth payload hp,
    Nat.mul_div_cancel depth (width_pos hm hw)]

theorem decodeVariableRow_encode {m depth width : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decodeVariableRow m width (encode width h) = row h := by
  rw [decodeVariableRow_generated hm hw _ (encode_mem width h)]
  exact decodeRow_encode hm width hw h

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem accepts_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses) rows x =
      HashSelect.accepts (HashSelect.cnfRowAccept clauses) (rows.map (decode m)) x := by
  simp [HashSelect.accepts, rowAccept, List.all_map, Function.comp_def]

theorem mass_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) :
    HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses) rows =
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
        (rows.map (decode m)) := by
  simp only [HashSelect.mass, accepts_decode]

theorem history_accepts_iff {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) x = true ↔
        ∀ e, (clauses e).eval x = true := by
  rw [accepts_decode]
  apply HashSelect.cnf_mass_zero_iff
  rw [← mass_decode]
  exact history_mass_zero clauses hm depth initial hcode

/-- Exact accepted-assignment count over the ambient Fin n, without deleting
unused coordinates or taking a low binary bit. -/
theorem history_count_eq {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    HashSelect.acceptedCount (rowAccept clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) =
        ∑ x : SAT.Assignment (Fin n), if ∀ e, (clauses e).eval x = true then 1 else 0 := by
  unfold HashSelect.acceptedCount
  apply Finset.sum_congr rfl
  intro x _
  simp only [history_accepts_iff clauses hm depth initial hcode x]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
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

theorem listCandidate_terms {m : ℕ} (row : List (Fin m × ZMod 3)) :
    HashInputProgram.candidateTerms (listCandidate row) = row := by
  simp [HashInputProgram.candidateTerms, listCandidate]

theorem listCandidate_encode {m : ℕ} (width : ℕ) (row : List (Fin m × ZMod 3)) :
    HashFamilyPayload.encode width (listCandidate row) = (CodeRowsProgram.rowPayload width m row).reverse := by
  rw [← HashInputProgram.candidate_rawInput, listCandidate_terms]
  rfl

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual serializer's payloads satisfy the initial-code hypothesis of
the actual generated-order selector. Repeated and zero raw slots are retained;
their finite-field coefficients are combined only in the semantic decoder. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open scoped BigOperators
open LeafScopeResourceBounds

theorem listCandidate_row {m : ℕ} (slots : List (Fin m × ZMod 3)) :
    HashFamily.row (listCandidate slots) = CodeRowsProgram.coefficient slots := by
  funext i
  have h := congrArg (fun xs : List (Fin m × ZMod 3) =>
    (xs.map (fun z => if z.1=i then z.2 else 0)).sum) (List.ofFn_get slots)
  change (∑ x, if (slots.get x).1 = i then (slots.get x).2 else 0) =
    (slots.map (fun z => if z.1 = i then z.2 else 0)).sum
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun z => if z.1 = i then z.2 else 0) ∘ slots.get)).sum = _
  rw [← List.map_ofFn]
  exact h

theorem decode_initial_payload {m width : ℕ} (hm : 0 < m) (hwidth : 3*m ≤ 2^width)
    (slots : List (Fin m × ZMod 3)) :
    HashFamilyPayload.decodeVariableRow m width (CodeRowsProgram.rowPayload width m slots).reverse =
      CodeRowsProgram.coefficient slots := by
  rw [← listCandidate_encode,HashFamilyPayload.decodeVariableRow_encode hm hwidth,
    listCandidate_row]

theorem decode_initial_rows {m width : ℕ} (hm : 0 < m) (hwidth : 3*m ≤ 2^width)
    (rows : List (List (Fin m × ZMod 3))) :
    (initialPayloads width rows).map (HashFamilyPayload.decodeVariableRow m width) =
      rows.map CodeRowsProgram.coefficient := by
  simp only [initialPayloads,List.map_map]
  apply List.map_congr_left
  intro slots _
  exact decode_initial_payload hm hwidth slots

theorem initial_kernel_bound {m B width : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hwidth : 3*m ≤ 2^width) (s : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (v : Fin m → ZMod 3)
    (hv : ∀ r ∈ (initialPayloads width (CodeRowsProgram.serializedRows m s Q)).map
        (HashFamilyPayload.decodeVariableRow m width), (∑ e, r e*v e)=0)
    (hv0 : v≠0) : m ≤ SparseCode.distanceDenom m B*SparseCode.weight v := by
  rw [decode_initial_rows hm hwidth] at hv
  apply CodeRowsProgram.serializedRows_kernel_bound hm hB s Q hs hQ v
  · intro row hrow
    exact hv _ (List.mem_map.mpr ⟨row,hrow,rfl⟩)
  · exact hv0

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem initial_code_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1))
    (v : HashSelect.Row m)
    (hv : ∀ r ∈ (initial shifts Q).map (decode m), (∑ e, r e * v e) = 0)
    (hv0 : v ≠ 0) : m ≤ SparseCode.distanceDenom m B * SparseCode.weight v :=
  LeafOuterProgram.initial_kernel_bound hm hB (HashCandidates.digitWidth_sufficient m)
    shifts Q hs hQ v hv hv0

/-- Goodness and distance are properties of the actually returned candidates;
no identity with the old chosenGraph/chosenLocal definitions is required. -/
theorem supplied_history_count_eq {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1)) :
    HashSelect.acceptedCount (rowAccept clauses)
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) (HashSelect.loopCap n m)) =
        ∑ x : SAT.Assignment (Fin n), if ∀ e, (clauses e).eval x = true then 1 else 0 :=
  history_count_eq clauses hm _ _ (initial_code_distance hm hB shifts Q hs hQ)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

/-- Indexing the original list gives its semantic clause set, including when
that list contains repeated clauses or repeated literals. -/
theorem indexed_image {n : ℕ} (F : RawCNF n) :
    Finset.univ.image (indexed F) = ExecCNF.formulaSet F := by
  ext C
  simp only [Finset.mem_image, Finset.mem_univ, true_and, ExecCNF.mem_formulaSet]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨F.get i, List.get_mem F i, hi⟩
  · rintro ⟨D,hD,hC⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hD
    exact ⟨i,hC⟩

theorem indexed_eval {n : ℕ} (F : RawCNF n) (x : SAT.Assignment (Fin n)) :
    (∀ i, (indexed F i).eval x = true) ↔ SAT.CNF.eval x (ExecCNF.formulaSet F) = true := by
  rw [← indexed_image F]
  simp

/-- The sum ranges over all assignments on the declared Fin n, including
coordinates unused by every clause. -/
theorem rawCount_sum {n : ℕ} (F : RawCNF n) :
    rawCount F = ∑ x : SAT.Assignment (Fin n),
      if ∀ i, (indexed F i).eval x = true then 1 else 0 := by
  unfold rawCount SAT.count SAT.satisfyingAssignments
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [(indexed_eval F x).symm]

/-- This is the full unmarked accepted count, not the violation mass or a
single marked query's count. -/
theorem history_count_oai {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1)) :
    HashSelect.acceptedCount (HashGreedyCNF.rowAccept (indexed F))
      (HashGreedyCNF.history (indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) = rawCount F := by
  rw [HashGreedyCode.supplied_history_count_eq (indexed F) hm hB shifts Q hs hQ]
  exact (rawCount_sum F).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count_oai
