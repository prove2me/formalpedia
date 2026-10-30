-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:49:23.912589+00:00
-- url     : https://prove2.me/submissions/16975949-1264-4c6c-b7a0-5e768f451aa6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S050

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed eight-label program counts nonzero two-bit cells. The input is
consumed and the count is emitted in unary. This is an actual support counter,
not a unit-cost application of `List.countP`. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram
open scoped BigOperators

theorem ternaryCell_encoding (x : SparseCode.F3) :
    [(ternaryCell x).1, (ternaryCell x).2] =
      SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem framedCellStream_ternary (xs : List SparseCode.F3) :
    framedCellStream (xs.map ternaryCell) =
      xs.flatMap (fun x => Encoding.frame (SubexpEnumerationPayload.scalarBits x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, framedCellStream, List.flatMap_cons, ih,
        ← ternaryCell_encoding]
      rfl

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

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

theorem matrixWords_eq_words_flatten (rows : List (List (List Bool))) :
    matrixWords rows = words rows.flatten := by
  induction rows with
  | nil => rfl
  | cons ys rows ih => simp [matrixWords, List.flatten_cons, words_append, ih]

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

theorem scalarFrames_ternary (xs : List SparseCode.F3) :
    scalarFrames xs = framedCellStream (xs.map ternaryCell) := by
  rw [framedCellStream_ternary]
  simp only [scalarFrames ]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.map_cons, List.flatMap_cons, scalarWord_eq,
        MatrixProgramSupport.words] using
        congrArg (fun rest => Encoding.frame (SubexpEnumerationPayload.scalarBits x) ++ rest) ih

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramRepresentation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-for-byte agreement between generated candidates and arithmetic inputs.
These identities remove recoding from the search interface; they are not
assumptions that a rearrangement of an existing tape is cost-free. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem words_eq_flatMap (xs : List (List Bool)) :
    Subexp.MatrixProgramSupport.words xs = xs.flatMap Encoding.frame := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Subexp.MatrixProgramSupport.words, ih]

theorem framedVector_eq_scalarFrames {p d : ℕ} [Fact p.Prime]
    (v : Fin d → ZMod p) : framedVector v = scalarFrames (List.ofFn v) := by
  simp [framedVector, SubexpTupleRefinement.encodeTuple,
    StackEncoding.encodeDataStack_eq_flatMap, framedScalarCode,
    Subexp.BasisTransposeProgram.framedCode, scalarFrames,
    words_eq_flatMap, SubexpEnumerationPayload.scalarCode]
  rw [← List.map_ofFn]
  simp only [List.flatMap_map, scalarWord_eq]

theorem flattenMatrix_ofFn {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) :
    List.ofFn (flattenMatrix M) =
      (List.ofFn fun i => List.ofFn fun j => M i j).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hidx : (finProdFinEquiv (i,j)).val = i.val * cols + j.val := by
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  change flattenMatrix M ⟨i.val * cols + j.val, _⟩ = M i j
  rw [show (⟨i.val * cols + j.val, _⟩ : Fin (rows * cols)) =
      finProdFinEquiv (i,j) from Fin.ext hidx.symm]
  simp [flattenMatrix]

theorem framedMatrix_eq_matrixFrames {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : framedMatrix M = matrixFrames M := by
  rw [framedMatrix, framedVector_eq_scalarFrames, flattenMatrix_ofFn]
  simp [scalarFrames, matrixFrames, words_eq_flatMap,
    Subexp.MatrixVectorProgram.matrixWords_eq_words_flatten,
    List.map_flatten, List.map_ofFn, Function.comp_def]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform bit lengths for every matrix and word, including rejected
candidates. These bounds do not depend on matrix entries or search success. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp

theorem framedCellStream_length (cells : List (Bool × Bool)) :
    (framedCellStream cells).length = 5 * cells.length := by
  induction cells with
  | nil => rfl
  | cons x xs ih => simp [framedCellStream, ih]; omega

theorem scalarFrames_ternary_length (xs : List SparseCode.F3) :
    (scalarFrames xs).length = 5 * xs.length := by
  rw [scalarFrames_ternary, framedCellStream_length, List.length_map]

theorem matrixFrames_ternary_length_oai {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) : (matrixFrames Q).length = 5 * (t * D) := by
  rw [← framedMatrix_eq_matrixFrames, framedMatrix, framedVector_eq_scalarFrames,
    scalarFrames_ternary_length, List.length_ofFn]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length_oai
