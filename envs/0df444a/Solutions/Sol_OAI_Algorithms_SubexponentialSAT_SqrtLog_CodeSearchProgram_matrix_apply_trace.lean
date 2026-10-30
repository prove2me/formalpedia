-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:00:23.726122+00:00
-- url     : https://prove2.me/submissions/de3e27d2-8048-4d89-af81-e5be257c6972

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S069
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixVectorProgram_matrix_trace

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

theorem result_widths {p B : ℕ} {xs : List (List Bool)}
    {rows : List (List (List Bool))} {zs : List (List Bool)}
    (h : List.Forall₂ (RowResult p B xs) rows zs) : ∀ z ∈ zs, z.length = B := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hh.1
    · exact ih z hz

theorem result_canonical {p B : ℕ} {xs : List (List Bool)}
    {rows : List (List (List Bool))} {zs : List (List Bool)}
    (h : List.Forall₂ (RowResult p B xs) rows zs) : ∀ z ∈ zs, BinaryArithmetic.toNat z < p := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hh.2.1
    · exact ih z hz

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixWordEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical prime-field words for the local matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixWordEncoding

open BinaryArithmetic SubexpLiftRing

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem modulus_capacity : p ≤ 2 ^ width p := by
  simpa only [width, pow_one] using modulus_le_width p 1

theorem word_value (a : ZMod p) : BinaryArithmetic.toNat (word p a) = a.val :=
  toNat_fixedBits_of_lt _ _ (a.val_lt.trans_le (modulus_capacity p))

theorem word_field_value (a : ZMod p) : (BinaryArithmetic.toNat (word p a) : ZMod p) = a := by
  rw [word_value]
  simp

/-- A canonical machine output of the expected width is exactly the
corresponding field word, not merely a congruent numeric representative. -/
theorem word_unique (a : ZMod p) (bits : List Bool)
    (hl : bits.length = width p) (hc : BinaryArithmetic.toNat bits < p)
    (hv : (BinaryArithmetic.toNat bits : ZMod p) = a) : bits = word p a := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact hl.trans (word_length p a).symm
  · calc
      BinaryArithmetic.toNat bits = (BinaryArithmetic.toNat bits : ZMod p).val := (ZMod.val_natCast_of_lt hc).symm
      _ = a.val := congrArg ZMod.val hv
      _ = BinaryArithmetic.toNat (word p a) := (word_value p a).symm

theorem words_unique (bits : List (List Bool)) (values : List (ZMod p))
    (hl : ∀ w ∈ bits, w.length = width p) (hc : ∀ w ∈ bits, BinaryArithmetic.toNat w < p)
    (hv : bits.map (fun w => (BinaryArithmetic.toNat w : ZMod p)) = values) :
    bits = values.map (word p) := by
  rw [← hv, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, Function.comp_apply]
    exact word_unique p _ _ (hl _ (List.getElem_mem hi)) (hc _ (List.getElem_mem hi)) rfl

omit [Fact p.Prime] in
theorem modulus_value : BinaryArithmetic.toNat (modulus p) = p := by
  apply toNat_fixedBits_of_lt
  have hc := modulus_capacity p
  have hp : 0 < 2 ^ width p := pow_pos (by decide) _
  rw [pow_succ]
  omega

theorem modulus_positive : 0 < BinaryArithmetic.toNat (modulus p) := by
  rw [modulus_value]
  exact (Fact.out : p.Prime).pos

@[simp] theorem zero_value : BinaryArithmetic.toNat (zero p) = 0 := by
  rw [zero, word_value]
  simp

end SubexponentialSAT.Subexp.MatrixWordEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Mathematical interpretation of the actual encoded matrix-program outputs. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSemantics

open BinaryArithmetic MatrixProgram MatrixVectorProgram
open scoped BigOperators

theorem dotValue_ofFn (p : ℕ) {N : ℕ} (x y : Fin N → List Bool) :
    dotValue p (List.ofFn x) (List.ofFn y) =
      ∑ i, (BinaryArithmetic.toNat (x i) : ZMod p) * (BinaryArithmetic.toNat (y i) : ZMod p) := by
  induction N with
  | zero => simp [dotValue]
  | succ N ih =>
    simp only [List.ofFn_succ, dotValue, Fin.sum_univ_succ, ih]

theorem encoded_dot (p : ℕ) (code : ZMod p → List Bool)
    (hcode : ∀ a, (BinaryArithmetic.toNat (code a) : ZMod p) = a)
    {N : ℕ} (x y : Fin N → ZMod p) :
    dotValue p (List.ofFn fun i => code (x i)) (List.ofFn fun i => code (y i)) =
      ∑ i, x i * y i := by
  rw [dotValue_ofFn]
  simp only [hcode]

private theorem mapped_of_forall₂ {A B C : Type*} (R : A → B → Prop)
    (f : A → C) (g : B → C) {as : List A} {bs : List B}
    (h : List.Forall₂ R as bs) (hv : ∀ a b, R a b → g b = f a) :
    bs.map g = as.map f := by
  induction h with
  | nil => rfl
  | cons hh ht ih => simp only [List.map_cons, hv _ _ hh, ih]

/-- The program's elementwise result relation is the ordinary matrix-vector
product for any faithful scalar encoding. Canonicality is additionally kept
in the relation for the later executable zero test. -/
theorem matrix_result_values (p B : ℕ) (code : ZMod p → List Bool)
    (hcode : ∀ a, (BinaryArithmetic.toNat (code a) : ZMod p) = a)
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (x : Fin N → ZMod p)
    (results : List (List Bool))
    (h : List.Forall₂
      (RowResult p B (List.ofFn fun i => code (x i)))
      (List.ofFn fun j => List.ofFn fun i => code (M j i)) results) :
    results.map (fun z => (BinaryArithmetic.toNat z : ZMod p)) =
      List.ofFn (fun j => ∑ i, M j i * x i) := by
  have hm := mapped_of_forall₂
    (RowResult p B (List.ofFn fun i => code (x i)))
    (fun row => dotValue p (List.ofFn fun i => code (x i)) row)
    (fun z => (BinaryArithmetic.toNat z : ZMod p)) h (fun _ _ hz => hz.2.2)
  rw [hm]
  simp only [List.map_ofFn, Function.comp_def, encoded_dot p code hcode]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- With the canonical prime-field code, the output frames contain exactly
the standard words for the mathematical product. This also justifies using
the first product's actual bytes as the second product's input. -/
theorem matrix_result_words (p : ℕ) [Fact p.Prime]
    {m N : ℕ} (M : Fin m → Fin N → ZMod p) (x : Fin N → ZMod p)
    (results : List (List Bool))
    (h : List.Forall₂
      (RowResult p (MatrixWordEncoding.width p)
        (List.ofFn fun i => MatrixWordEncoding.word p (x i)))
      (List.ofFn fun j => List.ofFn fun i => MatrixWordEncoding.word p (M j i)) results) :
    results = List.ofFn (fun j => MatrixWordEncoding.word p (∑ i, M j i * x i)) := by
  have hv := matrix_result_values p (MatrixWordEncoding.width p) (MatrixWordEncoding.word p)
    (MatrixWordEncoding.word_field_value p) M x results h
  have he := MatrixWordEncoding.words_unique p results (List.ofFn fun j => ∑ i, M j i * x i)
    (result_widths h) (result_canonical h) hv
  simpa only [List.map_ofFn, Function.comp_def] using he

end SubexponentialSAT.Subexp.MatrixProgramSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

/-- The field result is connected to the exact bytes produced by the program.
The theorem includes parsing, every failed or successful arithmetic step,
the runtime row loop, and reversal into forward output order. -/
theorem matrix_apply_trace_oai {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p) (regs : Fin 8 → Bool) :
    ∃ n rf, n ≤ MatrixVectorProgram.matrixBudget t D (MatrixWordEncoding.width p) ∧
      Trace MatrixVectorProgram.matrixProgram n
        ((matrixInput Q x regs).withPC (some MatrixVectorProgram.matrixProgram.entry))
        ((matrixOutput Q x rf).withPC none) := by
  have hx : ∀ w ∈ (List.ofFn fun j => MatrixWordEncoding.word p (x j)),
      w.length = MatrixWordEncoding.width p := by
    intro w hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact MatrixWordEncoding.word_length p _
  have hrows : ∀ row ∈ (List.ofFn fun i =>
      List.ofFn fun j => MatrixWordEncoding.word p (Q i j)),
      (List.ofFn fun j => MatrixWordEncoding.word p (x j)).length = row.length ∧
      ∀ w ∈ row, w.length = MatrixWordEncoding.width p := by
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    constructor
    · simp
    · intro w hw
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      exact MatrixWordEncoding.word_length p _
  obtain ⟨n, hn, rf, results, ht, hrel⟩ := MatrixVectorProgram.matrix_trace
    (List.ofFn fun j => MatrixWordEncoding.word p (x j))
    (List.ofFn fun i => List.ofFn fun j => MatrixWordEncoding.word p (Q i j))
    (MatrixWordEncoding.width p) (MatrixWordEncoding.modulus p) (MatrixWordEncoding.zero p)
    hx hrows (MatrixWordEncoding.zero_length p) (MatrixWordEncoding.zero_value p)
    (MatrixWordEncoding.modulus_length p).le (MatrixWordEncoding.modulus_positive p)
    (by rw [MatrixWordEncoding.modulus_value]; exact MatrixWordEncoding.modulus_capacity p)
    regs []
  rw [MatrixWordEncoding.modulus_value] at hrel
  have heq := MatrixProgramSemantics.matrix_result_words p Q x results hrel
  refine ⟨n, rf, by simpa using hn, ?_⟩
  simpa [matrixInput, matrixOutput, matrixFrames, scalarFrames, heq,
    List.map_ofFn, Function.comp_def] using ht

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace_oai
