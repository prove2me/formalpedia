-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:19:17.465626+00:00
-- url     : https://prove2.me/submissions/9dac4d48-96a5-41f8-982c-87da3d97453a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrixFrames_ternary_length

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

theorem modulus_three : MatrixWordEncoding.modulus 3 = [true,true,false] := by
  norm_num [MatrixWordEncoding.modulus, MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth, SubexpLiftRing.fixedBits]

theorem zero_three : MatrixWordEncoding.zero 3 = [false,false] := by
  norm_num [MatrixWordEncoding.zero, MatrixWordEncoding.word, MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth, SubexpLiftRing.fixedBits]

theorem wordInput_length_le_oai {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (regs : Fin 8 → Bool) (i : Fin 18) :
    ((extendMatrixState (matrixInput Q x regs) d []).stacks i).length ≤
      wordInputSpan t D d := by
  have hm := matrixFrames_ternary_length Q
  have hx := scalarFrames_ternary_length (List.ofFn x)
  simp only [List.length_ofFn] at hx
  have h16 : (16 : Fin 18).val = 16 := rfl
  fin_cases i <;>
    norm_num [extendMatrixState, matrixInput, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks,
      modulus_three, zero_three, wordInputSpan, hm, hx, Fin.ext_iff, h16] <;> omega

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le_oai
