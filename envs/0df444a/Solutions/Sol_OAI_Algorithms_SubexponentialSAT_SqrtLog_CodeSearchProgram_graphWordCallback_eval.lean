-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:13.986685+00:00
-- url     : https://prove2.me/submissions/9b6a8fad-4872-4574-9e55-7f708642fdeb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S102
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphWord_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_preparedGraphWord_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem clearMany_reg_frame {S : ℕ} (ps : List (Fin S)) (a : Data S) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (clearManyState ps a).regs i = a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (clearState p a)).trans
      (StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1)

end SubexponentialSAT.SubexpSetupStorage

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

theorem graphLiteralCommand_eval (a : GraphSearchState) :
    Eval graphLiteralCommand 8 a (graphLiteralState a) := by
  exact (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

theorem prepareGraphWord_eval (a : GraphSearchState) (ht : a.stacks 35 = []) :
    Eval prepareGraphWordCommand (prepareGraphWordCost a) a (preparedGraphWord a) := by
  have hp : ∀ p ∈ graphInputMoves, p.1 ≠ p.2 ∧ p.1 ≠ (35 : Fin 36) ∧ 35 ≠ p.2 := by
    intro p hp
    simp only [graphInputMoves, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hc := copyMany_eval 35 graphInputMoves a hp ht
  have hx := SubexpScanPrimitives.transfer_eval (copyManyState graphInputMoves a)
    34 12 0 1 (by decide) (by decide)
  have hl := graphLiteralCommand_eval (SubexpScanPrimitives.afterTransfer
    (copyManyState graphInputMoves a) 34 12 0 1)
  have h := hc.seq (hx.seq hl)
  convert h using 1 <;> simp [ preparedGraphWord, prepareGraphWordCost,
    graphInputMoves, copyManyCost, copyManyState, copyState, StackRoutines.copyStacks,
    Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

theorem graphWorkPorts_mem (i : Fin 36) : i ∈ graphWorkPorts ↔ i.val < 29 := by
  simp only [graphWorkPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro h; exact ⟨⟨i.val,h⟩, Fin.ext rfl⟩

theorem preparedGraphWord_frame (a : GraphSearchState) (i : Fin 36)
    (hi : 29 ≤ i.val) (hp : i ≠ 34) : (preparedGraphWord a).stacks i = a.stacks i := by
  have h11 : i ≠ 11 := by intro h; subst i; omega
  have h12 : i ≠ 12 := by intro h; subst i; omega
  have h15 : i ≠ 15 := by intro h; subst i; omega
  have h16 : i ≠ 16 := by intro h; subst i; omega
  have h17 : i ≠ 17 := by intro h; subst i; omega
  have h5 : i ≠ 5 := by intro h; subst i; omega
  have h14 : i ≠ 14 := by intro h; subst i; omega
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    h11,h12,h15,h16,h17,h5,h14,hp]

theorem preparedGraphWord_payload (a : GraphSearchState) : (preparedGraphWord a).stacks 34 = [] := by
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg]

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

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

private theorem prepared_register_frame_p1 (a : GraphSearchState) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (preparedGraphWord a).regs i = a.regs i := by
  simp [preparedGraphWord, graphLiteralState, graphInputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    readRegs, h0, h1]

private theorem work_stack_frame_p1 (frame : GraphSearchState) (out : GraphWordState)
    (i : Fin 36) (hi : 29 ≤ i.val) :
    (embedState id graphWordStacks frame out).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [graphWordStacks] at hv
  omega

private theorem clearManyCost_le_on_p1 (ps : List (Fin 36)) (a : GraphSearchState) (B : ℕ)
    (ha : ∀ i ∈ ps, (a.stacks i).length ≤ B) :
    clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
      have hc := ih (clearState p a) (by
        intro i hi
        by_cases hip : i = p
        · simp [clearState, hip]
        · simpa [clearState, hip] using ha i (by simp [hi]))
      have hp := ha p (by simp)
      simp only [clearManyCost, List.length_cons]
      nlinarith

/-- Every character uses the same closed bit predicate, whether or not this
candidate graph is good. The cleanup charge includes all arithmetic scratch. -/
theorem graphWordCallback_eval_oai {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : GraphSearchState) (he : GraphWorkEmpty a)
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : GraphSearchState), n ≤ graphCallbackBudget D r qbits.length Dbits.length ∧
      Eval graphWordCallback n a out ∧ GraphWorkEmpty out ∧
      out.regs 15 = decide (graphWordRejects s x q) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 34 = [] ∧
      (∀ i : Fin 36, 29 ≤ i.val → i ≠ 34 → out.stacks i = a.stacks i) := by
  let initial := projectState id graphWordStacks (preparedGraphWord a)
  have hp := prepareGraphWord_eval a htmp
  obtain ⟨nw,small,hnw,hw,hf,hqout,hDout,hclean,h13,h14⟩ :=
    graphWord_eval s x q qbits Dbits hqv hDv initial
      (preparedGraphWord_project s x qbits Dbits a he hm ht hq hD hx)
      (preparedGraphWord_scratch a he)
  have hi := invoke_eval graphWordProgram id graphWordStacks Function.injective_id
    (Fin.castAdd_injective _ _) (preparedGraphWord a) small (compiled_halt_trace hw 11 9)
  let middle := embedState id graphWordStacks (preparedGraphWord a) small
  let out := clearManyState graphWorkPorts middle
  have hc := clearMany_eval graphWorkPorts middle
  have hsmall (i : Fin 29) : (small.stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length + graphWordBudget D r qbits.length Dbits.length := by
    have h := SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace hw 11 9) i
    have hinput := preparedGraphWord_length_le s x qbits Dbits a he hm ht hq hD hx i
    change (small.stacks i).length ≤ (initial.stacks i).length + (nw+1) at h
    change (initial.stacks i).length ≤ graphInputSpan D r qbits.length Dbits.length at hinput
    omega
  have hcleanup := clearManyCost_le_on_p1 graphWorkPorts middle
    (graphInputSpan D r qbits.length Dbits.length + graphWordBudget D r qbits.length Dbits.length) (by
      intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      rw [show middle.stacks (graphWordStacks j) = small.stacks j from
        embedState_stack id graphWordStacks (preparedGraphWord a) small (Fin.castAdd_injective _ _) j]
      exact hsmall j)
  have hprep : prepareGraphWordCost a =
      35 * (D * r) + 7 * D + 7 * qbits.length + 7 * Dbits.length + 15 * r + 31 := by
    simp only [prepareGraphWordCost,hm,ht,hq,hD,hx,List.length_reverse,
      List.length_replicate,scalarFrames_binary_length,matrixFrames_binary_length,List.length_ofFn]
    ring
  have hclen : graphWorkPorts.length = 29 := by simp [graphWorkPorts]
  rw [hclen] at hcleanup
  refine ⟨prepareGraphWordCost a + (nw+1+clearManyCost graphWorkPorts middle),out,?_,
    hp.seq (hi.seq hc),?_,?_,?_,?_,?_,?_⟩
  · rw [hprep]; unfold graphCallbackBudget; omega
  · intro i
    have hm : graphWordStacks i ∈ graphWorkPorts := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [clearMany_stacks,ite_eq_left hm]
  · rw [show out.regs 15 = middle.regs 15 from
      clearMany_reg_frame graphWorkPorts middle 15 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 15).trans hf
  · rw [show out.regs 13 = middle.regs 13 from
      clearMany_reg_frame graphWorkPorts middle 13 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 13).trans (h13.trans (prepared_register_frame_p1 a 13 (by decide) (by decide)))
  · rw [show out.regs 14 = middle.regs 14 from
      clearMany_reg_frame graphWorkPorts middle 14 (by decide) (by decide)]
    exact (embedState_register id graphWordStacks (preparedGraphWord a) small
      Function.injective_id 14).trans (h14.trans (prepared_register_frame_p1 a 14 (by decide) (by decide)))
  · rw [clearMany_stacks,ite_eq_right (by rw [graphWorkPorts_mem]; decide)]
    rw [work_stack_frame_p1 _ _ _ (by decide)]
    exact preparedGraphWord_payload a
  · intro i hi hne
    rw [clearMany_stacks,ite_eq_right (by rw [graphWorkPorts_mem]; omega)]
    rw [work_stack_frame_p1 _ _ _ hi]
    exact preparedGraphWord_frame a i hi hne

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval_oai
