-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:09:37.154049+00:00
-- url     : https://prove2.me/submissions/6637e4aa-9847-4dff-bed9-d4fd9a2ea106

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashSelect_initial_coverage_of_code
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCNF_reference_covered

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

theorem mass_le [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) (m : ℕ)
    (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows ≤ Fintype.card X * m := by
  calc
    mass rowAccept weight rows ≤ ∑ _x : X, m := by
      apply Finset.sum_le_sum
      intro x _
      cases hx : accepts rowAccept rows x <;> simp [ hw x]
    _ = Fintype.card X * m := by simp

theorem sum_trial_mass [Fintype X] [Fintype I]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : I → R) (rows : List R) :
    (∑ i, mass rowAccept weight (family i :: rows)) =
      ∑ x, if accepts rowAccept rows x then
        survivingCandidates rowAccept family x * weight x else 0 := by
  simp only [mass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases ha : accepts rowAccept rows x
  · simp [ha, accepts_cons]
  · simp only [accepts_cons, ha, Bool.and_true, ↓reduceIte]
    rw [survivingCandidates, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases hr : rowAccept (family i) x <;> simp []

theorem average_trial_contraction [Fintype X] [Fintype I]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : I → R) (rows : List R)
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * Fintype.card I) :
    3 * (∑ i, mass rowAccept weight (family i :: rows)) ≤
      2 * Fintype.card I * mass rowAccept weight rows := by
  rw [sum_trial_mass, mass, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  cases ha : accepts rowAccept rows x
  · simp []
  · simp only [ ↓reduceIte]
    by_cases hw : weight x = 0
    · simp [hw]
    · have h := Nat.mul_le_mul_right (weight x)
        (hcoverage x ha (Nat.pos_of_ne_zero hw))
      simpa [Nat.mul_assoc] using h

end SubexponentialSAT.SqrtLog.HashSelect

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

theorem best_le_seed (score : R → ℕ) (seed : R) (rs : List R) :
    score (best score seed rs) ≤ score seed := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    split_ifs with h
    · exact (ih r).trans (Nat.le_of_lt h)
    · exact ih seed

theorem best_le_member (score : R → ℕ) (seed : R) (rs : List R)
    (r : R) (hr : r ∈ rs) :
    score (best score seed rs) ≤ score r := by
  induction rs generalizing seed with
  | nil => simp at hr
  | cons a rs ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst a
      simp only [best]
      split_ifs with hs
      · exact best_le_seed score r rs
      · exact (best_le_seed score seed rs).trans (Nat.le_of_not_gt hs)
    · simp only [best]
      exact ih _ h

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

omit [DecidableEq V] [DecidableEq E] in
theorem violationWeight_le (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x ≤ Fintype.card E := by
  calc
    _ ≤ ∑ _e : E, 1 := Finset.sum_le_sum fun e _ => by split_ifs <;> omega
    _ = _ := by simp

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTermination
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entirely integer termination for the finite greedy selector. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

theorem two_step_halving {a b c : ℕ}
    (h₁ : 3 * b ≤ 2 * a) (h₂ : 3 * c ≤ 2 * b) : 2 * c ≤ a := by
  omega

theorem geometric_bound (f : ℕ → ℕ) (s : ℕ)
    (h : ∀ i < 2 * s, 3 * f (i + 1) ≤ 2 * f i) :
    2 ^ s * f (2 * s) ≤ f 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hi := ih (fun i hi => h i (by omega))
    have htwo : 2 * f (2 * s + 2) ≤ f (2 * s) :=
      two_step_halving (h (2 * s) (by omega)) (h (2 * s + 1) (by omega))
    calc
      2 ^ (s + 1) * f (2 * (s + 1)) = 2 ^ s * (2 * f (2 * s + 2)) := by
        rw [pow_succ]
        have ht : 2 * (s + 1) = 2 * s + 2 := by omega
        rw [ht]
        ring
      _ ≤ 2 ^ s * f (2 * s) := Nat.mul_le_mul_left _ htwo
      _ ≤ f 0 := hi

theorem zero_of_contraction (f : ℕ → ℕ) (s : ℕ)
    (h : ∀ i < 2 * s, 3 * f (i + 1) ≤ 2 * f i)
    (hstart : f 0 < 2 ^ s) : f (2 * s) = 0 := by
  have hg := (geometric_bound f s h).trans_lt hstart
  have hp : 0 < 2 ^ s := by positivity
  by_contra hn
  have hone : 1 ≤ f (2 * s) := Nat.one_le_iff_ne_zero.mpr hn
  have hlo := Nat.mul_le_mul_left (2 ^ s) hone
  simp only [Nat.mul_one] at hlo
  omega

theorem initial_mass_lt_cap_power {X R : Type*} [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight initial < 2 ^ (n + Nat.size m + 1) := by
  have hm := Nat.lt_size_self m
  calc
    mass rowAccept weight initial ≤ Fintype.card X * m :=
      mass_le rowAccept weight initial m hw
    _ ≤ 2 ^ n * m := Nat.mul_le_mul_right m hx
    _ < 2 ^ n * 2 ^ Nat.size m := Nat.mul_lt_mul_of_pos_left hm (by positivity)
    _ ≤ 2 ^ (n + Nat.size m + 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
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

/-- Averaging is over the reference ternary family, regardless of duplicates
or order in the stream used to find the minimizing row. -/
theorem contraction_of_minimum [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : Fin (c + 1) → R) (rows : List R) (selected : R)
    (hmin : ∀ i, mass rowAccept weight (selected :: rows) ≤
      mass rowAccept weight (family i :: rows))
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * mass rowAccept weight (selected :: rows) ≤ 2 * mass rowAccept weight rows := by
  have hsum : (c + 1) * mass rowAccept weight (selected :: rows) ≤
      ∑ i, mass rowAccept weight (family i :: rows) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmin i)
  have havg := average_trial_contraction rowAccept weight family rows
    (by simpa using hcoverage)
  have hmul : (c + 1) * (3 * mass rowAccept weight (selected :: rows)) ≤
      (c + 1) * (2 * mass rowAccept weight rows) := by
    calc
      _ = 3 * ((c + 1) * mass rowAccept weight (selected :: rows)) := by ring
      _ ≤ 3 * (∑ i, mass rowAccept weight (family i :: rows)) :=
        Nat.mul_le_mul_left 3 hsum
      _ ≤ 2 * Fintype.card (Fin (c + 1)) * mass rowAccept weight rows := havg
      _ = _ := by simp; ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- The retained unary round-count word is a sufficient common score width,
including weighted violation mass with up to `m` contributions per assignment. -/
theorem mass_lt_loopCap_capacity [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (rows : List R) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows < 2 ^ loopCap n m := by
  apply (initial_mass_lt_cap_power rowAccept weight rows n m hx hw).trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold loopCap
  omega

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem chosenEntry_le (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) (j : ℕ) (hj : j < 2 ^ C) :
    BinaryArgmin.value (chosenEntry entry C rows) ≤ BinaryArgmin.value (entry rows j) := by
  rw [chosenEntry_eq_best]
  exact HashSelect.best_le_member _ _ _ _ (List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩)

theorem iter_accepts_initial {X : Type*} (rowAccept : List Bool → X → Bool)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (initial : List (List Bool)) (q : ℕ) (x : X) :
    HashSelect.accepts rowAccept (HashSelectProgram.iter (nextRows entry C) q initial) x = true →
      HashSelect.accepts rowAccept initial x = true := by
  induction q with
  | zero => exact id
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    intro hx
    exact ih (Bool.and_eq_true_iff.mp hx).2

/-- Contraction averages over the original reference family. Extra decoded
binary candidates can repeat rows without changing the argument. -/
theorem chosen_contraction {X : Type*} [Fintype X] {c : ℕ}
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (rows : List (List Bool)) (family : Fin (c + 1) → List Bool)
    (hsound : ∀ j < 2 ^ C, BinaryArgmin.value (entry rows j) =
      HashSelect.mass rowAccept weight ((entry rows j).payload :: rows))
    (hcover : ∀ i, ∃ j < 2 ^ C, (entry rows j).payload = family i)
    (hcoverage : ∀ x, HashSelect.accepts rowAccept rows x = true → 0 < weight x →
      3 * HashSelect.survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * HashSelect.mass rowAccept weight (nextRows entry C rows) ≤
      2 * HashSelect.mass rowAccept weight rows := by
  have hchosen : BinaryArgmin.value (chosenEntry entry C rows) =
      HashSelect.mass rowAccept weight (nextRows entry C rows) := by
    obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
    simpa only [nextRows, he] using hsound j hj
  apply HashGreedy.contraction_of_minimum rowAccept weight family rows
    (chosenEntry entry C rows).payload
  · intro i
    obtain ⟨j, hj, he⟩ := hcover i
    have hm := chosenEntry_le entry C rows j hj
    rw [hchosen, hsound j hj, he] at hm
    exact hm
  · exact hcoverage

/-- The deterministic rows serialized by the actual outer run have zero
violation mass at the supplied original square-root-log loop cap. -/
theorem iter_mass_zero {X : Type*} [Fintype X] {c : ℕ}
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (family : Fin (c + 1) → List Bool) (initial : List (List Bool)) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hsound : ∀ q < HashSelect.loopCap n m, ∀ j < 2 ^ C,
      BinaryArgmin.value (entry (HashSelectProgram.iter (nextRows entry C) q initial) j) =
      HashSelect.mass rowAccept weight
        ((entry (HashSelectProgram.iter (nextRows entry C) q initial) j).payload ::
          HashSelectProgram.iter (nextRows entry C) q initial))
    (hcover : ∀ q < HashSelect.loopCap n m, ∀ i, ∃ j < 2 ^ C,
      (entry (HashSelectProgram.iter (nextRows entry C) q initial) j).payload = family i)
    (hcoverage : ∀ x, HashSelect.accepts rowAccept initial x = true → 0 < weight x →
      3 * HashSelect.survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    HashSelect.mass rowAccept weight
      (HashSelectProgram.iter (nextRows entry C) (HashSelect.loopCap n m) initial) = 0 := by
  apply HashSelect.zero_of_contraction
    (fun q => HashSelect.mass rowAccept weight (HashSelectProgram.iter (nextRows entry C) q initial))
    (n + Nat.size m + 1)
  · intro q hq
    rw [HashSelectProgram.iter_succ_apply]
    apply chosen_contraction rowAccept weight entry C _ family (hsound q hq) (hcover q hq)
    intro x ha hp
    exact hcoverage x (iter_accepts_initial rowAccept entry C initial q x ha) hp
  · exact HashSelect.initial_mass_lt_cap_power rowAccept weight initial n m hx hw

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

theorem entry_value {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    BinaryArgmin.value (entry rowAccept weight n m depth rows rank) =
      HashSelect.mass rowAccept weight (candidate m depth rank :: rows) := by
  rw [BinaryArgmin.value, entry, ← CounterPrograms.value_eq_toNat]
  exact ExecCNFTupleEnumeration.fixedBits_value _ _
    (HashGreedy.mass_lt_loopCap_capacity rowAccept weight _ n m hx hw)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
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

theorem decode_reference {m depth c : ℕ} (hm : 0 < m)
    (hcount : (3 * m) ^ depth = c + 1) (i : Fin (c + 1)) :
    decode m (reference hcount i) = HashSelect.tupleFamily hcount i := by
  exact HashFamilyPayload.decodeVariableRow_encode hm
    (HashCandidates.digitWidth_sufficient m) _

theorem accepts_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses) rows x =
      HashSelect.accepts (HashSelect.cnfRowAccept clauses) (rows.map (decode m)) x := by
  simp [HashSelect.accepts, rowAccept, List.all_map, Function.comp_def]

theorem entry_value {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (rows : List (List Bool)) (rank : ℕ) :
    BinaryArgmin.value (entry clauses depth rows rank) =
      HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
        ((entry clauses depth rows rank).payload :: rows) := by
  exact HashGreedyCandidate.entry_value _ _ n m depth rows rank
    (by simp [SAT.Assignment]) (fun x => by simpa using HashInput.violationWeight_le clauses x)

theorem initial_coverage {n m depth c : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (hcount : (3 * m) ^ depth = c + 1) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    ∀ x, HashSelect.accepts (rowAccept clauses) initial x = true →
      0 < HashInput.violationWeight clauses x →
      3 * HashSelect.survivingCandidates (rowAccept clauses) (reference hcount) x ≤
        2 * (c + 1) := by
  intro x ha hw
  have h := HashSelect.initial_coverage_of_code clauses hm hcount
    (initial.map (decode m)) hcode x ((accepts_decode clauses initial x) ▸ ha) hw
  simpa only [HashSelect.survivingCandidates, rowAccept, decode_reference hm] using h

/-- The exact payload/score accessor removes evaluator and family-coverage
premises from the contraction theorem. The initial code distance is supplied
by the independently constructed sparse code. -/
theorem history_mass_zero_oai {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) = 0 := by
  have hp : 0 < (3 * m) ^ depth := pow_pos (by omega) _
  have hc : (3 * m) ^ depth = ((3 * m) ^ depth - 1) + 1 := by omega
  apply HashGreedyRound.iter_mass_zero (rowAccept clauses)
    (HashInput.violationWeight clauses) (entry clauses depth)
    (HashCandidates.payloadWidth m depth) (reference hc) initial n m
  · simp [SAT.Assignment]
  · intro x
    simpa using HashInput.violationWeight_le clauses x
  · intro q _ j _
    exact entry_value clauses depth _ j
  · intro q _ i
    exact reference_covered clauses hc _ i
  · exact initial_coverage clauses hm hc initial hcode

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero_oai
