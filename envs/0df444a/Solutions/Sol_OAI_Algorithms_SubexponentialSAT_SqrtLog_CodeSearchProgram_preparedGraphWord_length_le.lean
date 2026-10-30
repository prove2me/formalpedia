-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:14.872569+00:00
-- url     : https://prove2.me/submissions/19ba3267-e8b7-4d8f-a2d8-7bd0f2075b4f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102

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

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

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

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramParity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Walsh parity counter uses the same fixed matrix/support code as the
ternary checker. Its output is a physical unary counter, not an abstract sum. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

theorem binaryCell_encoding (x : ZMod 2) :
    [(binaryCell x).1, (binaryCell x).2] = SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem scalarFrames_binary (xs : List (ZMod 2)) :
    scalarFrames xs = framedCellStream (xs.map binaryCell) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Encoding.frame (MatrixWordEncoding.word 2 x) ++ scalarFrames xs = _
      rw [scalarWord_eq, ← binaryCell_encoding, ih]
      rfl

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the Walsh character checker. The
matrix, row count, and two binary scalar words are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

theorem modulus_two : Subexp.MatrixWordEncoding.modulus 2 = [false,true,false] := by
  norm_num [Subexp.MatrixWordEncoding.modulus,Subexp.MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth,SubexpLiftRing.fixedBits]

theorem zero_two : Subexp.MatrixWordEncoding.zero 2 = [false,false] := by
  norm_num [Subexp.MatrixWordEncoding.zero,Subexp.MatrixWordEncoding.word,Subexp.MatrixWordEncoding.width,
    SubexpLiftRing.baseWidth,SubexpLiftRing.fixedBits]

theorem preparedGraphWord_project {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState) (he : GraphWorkEmpty a)
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
    projectState graphCountRegisters graphCountStacks
      (projectState id graphWordStacks (preparedGraphWord a)) =
      extendPairState (matrixInput s x ((preparedGraphWord a).regs ∘ graphCountRegisters)) qbits Dbits := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    have hei := he ⟨i.val,by omega⟩
    have he5 := he 5
    have he11 := he 11
    have he12 := he 12
    have he14 := he 14
    have he15 := he 15
    have he16 := he 16
    have he17 := he 17
    have hv0 : (0 : Fin 18).val = 0 := rfl
    have hv1 : (1 : Fin 18).val = 1 := rfl
    have hv2 : (2 : Fin 18).val = 2 := rfl
    have hv3 : (3 : Fin 18).val = 3 := rfl
    have hv4 : (4 : Fin 18).val = 4 := rfl
    have hv5 : (5 : Fin 18).val = 5 := rfl
    have hv6 : (6 : Fin 18).val = 6 := rfl
    have hv7 : (7 : Fin 18).val = 7 := rfl
    have hv8 : (8 : Fin 18).val = 8 := rfl
    have hv9 : (9 : Fin 18).val = 9 := rfl
    have hv10 : (10 : Fin 18).val = 10 := rfl
    have hv11 : (11 : Fin 18).val = 11 := rfl
    have hv12 : (12 : Fin 18).val = 12 := rfl
    have hv13 : (13 : Fin 18).val = 13 := rfl
    have hv14 : (14 : Fin 18).val = 14 := rfl
    have hv15 : (15 : Fin 18).val = 15 := rfl
    have hv16 : (16 : Fin 18).val = 16 := rfl
    have hv17 : (17 : Fin 18).val = 17 := rfl
    fin_cases i <;>
      simp_all [projectState,graphCountStacks,graphWordStacks,extendPairState,matrixInput,
        Subexp.MatrixScalarProgram.state,Subexp.MatrixScalarProgram.scalarStacks,
        preparedGraphWord,graphLiteralState,graphInputMoves,
        copyManyState,copyState,SubexpScanPrimitives.afterTransfer,
        StackRoutines.transferStacks,StackRoutines.copyStacks,
        Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,
modulus_two,zero_two]

theorem preparedGraphWord_scratch (a : GraphSearchState) (he : GraphWorkEmpty a)
    (i : Fin 29) (hi : 18 ≤ i.val) :
    (projectState id graphWordStacks (preparedGraphWord a)).stacks i = [] := by
  have h5 : graphWordStacks i ≠ 5 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h11 : graphWordStacks i ≠ 11 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h12 : graphWordStacks i ≠ 12 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h14 : graphWordStacks i ≠ 14 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h15 : graphWordStacks i ≠ 15 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h16 : graphWordStacks i ≠ 16 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h17 : graphWordStacks i ≠ 17 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  have h34 : graphWordStacks i ≠ 34 := by intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
  simpa [projectState,preparedGraphWord,graphLiteralState,graphInputMoves,
    copyManyState,copyState,SubexpScanPrimitives.afterTransfer,
    StackRoutines.transferStacks,StackRoutines.copyStacks,Atom.eval,Atom.instr,
    execInstr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    h5,h11,h12,h14,h15,h16,h17,h34] using he i

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem scalarFrames_binary_length (xs : List (ZMod 2)) :
    (scalarFrames xs).length = 5 * xs.length := by
  rw [scalarFrames_binary,framedCellStream_length,List.length_map]

theorem matrixFrames_binary_length {D r : ℕ} (s : Fin D → Cayley.Cube r) :
    (matrixFrames s).length = 5 * (D * r) := by
  rw [← framedMatrix_eq_matrixFrames,framedMatrix,framedVector_eq_scalarFrames,
    scalarFrames_binary_length,List.length_ofFn]

theorem graphInput_length_le {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (regs : Fin 8 → Bool) (qbits Dbits : List Bool) (i : Fin 18) :
    ((extendPairState (matrixInput s x regs) qbits Dbits).stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length := by
  have hm := matrixFrames_binary_length s
  have hx := scalarFrames_binary_length (List.ofFn x)
  simp only [List.length_ofFn] at hx
  have h16 : (16 : Fin 18).val = 16 := rfl
  have h17 : (17 : Fin 18).val = 17 := rfl
  fin_cases i <;>
    norm_num [extendPairState,matrixInput,MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
      modulus_two,zero_two,graphInputSpan,hm,hx,Fin.ext_iff,h16,h17] <;> omega

theorem preparedGraphWord_length_le_oai {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState)
    (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits)
    (hD : a.stacks 32 = Dbits) (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse)
    (i : Fin 29) :
    ((projectState id graphWordStacks (preparedGraphWord a)).stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length := by
  by_cases hi : i.val < 18
  · let j : Fin 18 := ⟨i.val,hi⟩
    have hij : graphCountStacks j = i := Fin.ext rfl
    have hp := congrArg (fun b : State 8 18 => (b.stacks j).length)
      (preparedGraphWord_project s x qbits Dbits a he hm ht hq hD hx)
    change ((projectState id graphWordStacks (preparedGraphWord a)).stacks (graphCountStacks j)).length = _ at hp
    rw [hij] at hp
    rw [hp]
    exact graphInput_length_le s x _ qbits Dbits j
  · rw [preparedGraphWord_scratch a he i (by omega)]
    exact Nat.zero_le _

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le_oai
