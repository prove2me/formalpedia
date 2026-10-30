-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:15.873392+00:00
-- url     : https://prove2.me/submissions/2162b136-93f3-4058-b4f5-b9dc75f4e15f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S102
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrixFrames_ternary_length
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_matrix_apply_trace
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_wordInput_length_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_wordTail_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

section Words

variable {C R : Type*} [Fintype C]

theorem weight_eq_sum (w : C → F3) :
    weight w = ∑ c, if w c ≠ 0 then 1 else 0 := by
  simp [weight, support, Finset.card_filter]

end Words

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

theorem ternaryCell_nonzero (x : SparseCode.F3) :
    ((ternaryCell x).1 || (ternaryCell x).2) = decide (x ≠ 0) := by
  fin_cases x <;> decide

theorem ternaryCell_encoding (x : SparseCode.F3) :
    [(ternaryCell x).1, (ternaryCell x).2] =
      SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem cellWeight_ternary (xs : List SparseCode.F3) :
    cellWeight (xs.map ternaryCell) =
      (xs.map fun x => if x ≠ 0 then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, cellWeight, ternaryCell_nonzero,
        decide_eq_true_eq, List.sum_cons, ih]
      omega

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

theorem ternary_product_weight_zero {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (x : Fin D → SparseCode.F3) :
    SparseCode.weight (fun i => ∑ j, Q i j * x j) = 0 ↔ SparseCode.IsCodeword Q x := by
  rw [SparseCode.weight_eq_zero_iff]
  simp only [funext_iff, Pi.zero_apply, SparseCode.IsCodeword, SparseCode.check]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete fixed-code test of one proposed short nonzero kernel word.
Matrix and word bytes, the row count, and the distance threshold are runtime
inputs. The protected stack 17 survives the call. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

private theorem extend_embed (base : State 8 16) (d : ℕ) (saved : List Bool) :
    embedState id matrixWordStacks (extendMatrixState base d saved) base =
      extendMatrixState base d saved := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendMatrixState, i.isLt]
  · intros; rfl
  · intros; rfl

private theorem extend_embed_result (initial final : State 8 16) (d : ℕ)
    (saved : List Bool) :
    embedState id matrixWordStacks (extendMatrixState initial d saved) final =
      extendMatrixState final d saved := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendMatrixState, i.isLt]
  · intro j hj
    exact False.elim (hj ⟨j,rfl⟩)
  · intro j hj
    have hnot : ¬ j.val < 16 := by
      intro h
      exact hj ⟨⟨j.val,h⟩, Fin.ext rfl⟩
    simp [extendMatrixState, hnot]

theorem word_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (regs : Fin 8 → Bool)
    (saved : List Bool) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ wordBudget t D ∧
      Eval wordCommand n (extendMatrixState (matrixInput Q x regs) d saved) next ∧
      next.regs 7 = decide (wordRejects Q x d) ∧ next.stacks 17 = saved := by
  obtain ⟨nm, rm, hnm, htm⟩ := matrix_apply_trace Q x regs
  have hm := eval_call_lifted MatrixVectorProgram.matrixProgram id matrixWordStacks
    (extendMatrixState (matrixInput Q x regs) d saved)
    Function.injective_id (Fin.castAdd_injective _ _) htm
  rw [extend_embed, extend_embed_result] at hm
  let y : Fin t → SparseCode.F3 := fun i => ∑ j, Q i j * x j
  let ys := (List.ofFn y).map ternaryCell
  let xs := (List.ofFn x).map ternaryCell
  have hy : (extendMatrixState (matrixOutput Q x rm) d saved).stacks 8 =
      framedCellStream ys := by
    change scalarFrames (List.ofFn y) = _
    exact scalarFrames_ternary _
  have hx : (extendMatrixState (matrixOutput Q x rm) d saved).stacks 12 =
      framedCellStream xs := by
    change scalarFrames (List.ofFn x) = _
    exact scalarFrames_ternary _
  obtain ⟨nt, out, hnt, ht, hflag, hsave⟩ := wordTail_eval ys xs d
    (extendMatrixState (matrixOutput Q x rm) d saved) hy hx (by rfl) (by rfl) (by rfl)
  have hxw : cellWeight xs = SparseCode.weight x := by
    rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
    rfl
  have hyw : cellWeight ys = SparseCode.weight y := by
    rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
    rfl
  refine ⟨nm + nt, out, ?_, hm.seq ht, ?_, hsave⟩
  · have hwidth : MatrixWordEncoding.width 3 = 2 := by
      norm_num [MatrixWordEncoding.width, SubexpLiftRing.baseWidth]
    rw [hwidth] at hnm
    have hyl : ys.length = t := by simp [ys]
    have hxl : xs.length = D := by simp [xs]
    rw [hyl, hxl] at hnt
    unfold wordBudget
    omega
  · rw [hxw, hyw] at hflag
    have hy0 : SparseCode.weight y = 0 ↔ SparseCode.IsCodeword Q x :=
      ternary_product_weight_zero Q x
    have hx0 : SparseCode.weight x ≠ 0 ↔ x ≠ 0 :=
      not_congr (SparseCode.weight_eq_zero_iff x)
    apply hflag.trans
    exact decide_eq_decide.mpr (and_congr hy0 (and_congr hx0 Iff.rfl))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the local-code word checker. The
matrix, row count, and threshold are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

theorem literalCommand_eval (a : SearchState) :
    Eval literalCommand 7 a (literalState a) := by
  exact (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq <|
    (Eval.base (.atom _ _)).seq <| (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

theorem prepareWord_eval (a : SearchState) (ht : a.stacks 23 = []) :
    Eval prepareWordCommand (prepareWordCost a) a (preparedWord a) := by
  have hp : ∀ p ∈ inputMoves, p.1 ≠ p.2 ∧ p.1 ≠ (23 : Fin 24) ∧ 23 ≠ p.2 := by
    intro p hp
    simp only [inputMoves, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  have hc := copyMany_eval 23 inputMoves a hp ht
  have hx := SubexpScanPrimitives.transfer_eval (copyManyState inputMoves a)
    22 12 0 1 (by decide) (by decide)
  have hl := literalCommand_eval (SubexpScanPrimitives.afterTransfer
    (copyManyState inputMoves a) 22 12 0 1)
  have h := hc.seq (hx.seq hl)
  convert h using 1 <;> simp [ preparedWord, prepareWordCost,
    inputMoves, copyManyCost, copyManyState, copyState, StackRoutines.copyStacks,
    Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

theorem workPorts_mem (i : Fin 24) : i ∈ workPorts ↔ i.val < 18 := by
  simp only [workPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro h; exact ⟨⟨i.val,h⟩, Fin.ext rfl⟩

theorem preparedWord_frame (a : SearchState) (i : Fin 24)
    (hi : 18 ≤ i.val) (hp : i ≠ 22) : (preparedWord a).stacks i = a.stacks i := by
  have h11 : i ≠ 11 := by intro h; subst i; omega
  have h12 : i ≠ 12 := by intro h; subst i; omega
  have h15 : i ≠ 15 := by intro h; subst i; omega
  have h16 : i ≠ 16 := by intro h; subst i; omega
  have h5 : i ≠ 5 := by intro h; subst i; omega
  have h14 : i ≠ 14 := by intro h; subst i; omega
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    h11,h12,h15,h16,h5,h14,hp]

theorem preparedWord_payload (a : SearchState) : (preparedWord a).stacks 22 = [] := by
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
    StackRoutines.copyStacks, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg ]

theorem preparedWord_project {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
    project wordRegisters wordStacks (preparedWord a) =
      extendMatrixState (matrixInput Q x ((preparedWord a).regs ∘ wordRegisters)) d [] := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    have hei := he i
    have he5 := he 5
    have he11 := he 11
    have he12 := he 12
    have he14 := he 14
    have he15 := he 15
    have he16 := he 16
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
      simp_all [project, wordStacks, extendMatrixState, matrixInput,
        Subexp.MatrixScalarProgram.state, Subexp.MatrixScalarProgram.scalarStacks, preparedWord, literalState, inputMoves,
        copyManyState, copyState, SubexpScanPrimitives.afterTransfer,
        StackRoutines.transferStacks, StackRoutines.copyStacks,
        Atom.eval, Atom.instr, execInstr, StructuredProgram.State.ofCfg, modulus_three, zero_three]


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

private theorem prepared_register_frame_p0 (a : SearchState) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (preparedWord a).regs i = a.regs i := by
  simp [preparedWord, literalState, inputMoves, copyManyState, copyState,
    SubexpScanPrimitives.afterTransfer, Atom.eval, Atom.instr, execInstr,
    StructuredProgram.State.ofCfg,
    readRegs, h0, h1]

private theorem work_register_frame (frame : SearchState) (out : ScanState)
    (i : Fin 16) (hi : 8 ≤ i.val) :
    (embedState wordRegisters wordStacks frame out).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [wordRegisters] at hv
  omega

private theorem work_stack_frame_p0 (frame : SearchState) (out : ScanState)
    (i : Fin 24) (hi : 18 ≤ i.val) :
    (embedState wordRegisters wordStacks frame out).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp [wordStacks] at hv
  omega

private theorem clearManyCost_le_on_p0 (ps : List (Fin 24)) (a : SearchState) (B : ℕ)
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

/-- Callback correctness is unconditional on the supplied matrix; a rejected
candidate is processed by the same bit program. The quantitative theorem is
separate so that cleanup, too, must be charged. -/
theorem wordCallback_eval_oai {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : SearchState), n ≤ callbackBudget t D d ∧
      Eval wordCallback n a out ∧ WorkEmpty out ∧
      out.regs 15 = decide (wordRejects Q x d) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 22 = [] ∧
      (∀ i : Fin 24, 18 ≤ i.val → i ≠ 22 → out.stacks i = a.stacks i) := by
  have hp := prepareWord_eval a htmp
  have hproj := preparedWord_project Q x d a he hm ht hd hx
  obtain ⟨nw, small, hnw, hw, hf, hs⟩ :=
    word_eval Q x d ((preparedWord a).regs ∘ wordRegisters) []
  have htrace := compiled_halt_trace hw 11 10
  rw [← hproj] at htrace
  have hi := invoke_eval wordProgram wordRegisters wordStacks
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) (preparedWord a) small htrace
  let middle := embedState wordRegisters wordStacks (preparedWord a) small
  let flagged := (Atom.copy 15 7).eval middle
  let out := clearManyState workPorts flagged
  have hc := clearMany_eval workPorts flagged
  have hsmall : ∀ i : Fin 18, (small.stacks i).length ≤
      wordInputSpan t D d + wordBudget t D := by
    intro i
    have h := Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace hw 11 10) i
    have hi := wordInput_length_le Q x d ((preparedWord a).regs ∘ wordRegisters) i
    change (small.stacks i).length ≤
      ((extendMatrixState (matrixInput Q x ((preparedWord a).regs ∘ wordRegisters)) d []).stacks i).length +
        (nw + 1) at h
    omega
  have hcleanup := clearManyCost_le_on_p0 workPorts flagged
    (wordInputSpan t D d + wordBudget t D) (by
      intro i hi
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      change (middle.stacks (wordStacks j)).length ≤ _
      rw [show middle.stacks (wordStacks j) = small.stacks j from
        embedState_stack wordRegisters wordStacks (preparedWord a) small
          (Fin.castAdd_injective _ _) j]
      exact hsmall j)
  have hprep : prepareWordCost a =
      35 * (t * D) + 7 * t + 7 * d + 15 * D + 25 := by
    simp only [prepareWordCost, hm, ht, hd, hx, List.length_reverse,
      List.length_replicate, scalarFrames_ternary_length, matrixFrames_ternary_length,
      List.length_ofFn]
    ring
  have hclen : workPorts.length = 18 := by simp [workPorts]
  rw [hclen] at hcleanup
  refine ⟨prepareWordCost a + (nw + 1 + (1 + clearManyCost workPorts flagged)), out,
    ?_, hp.seq (hi.seq ((Eval.base (.atom _ middle)).seq hc)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprep]
    unfold callbackBudget
    omega
  · intro i
    change (clearManyState workPorts flagged).stacks (wordStacks i) = []
    rw [clearMany_stacks, ite_eq_left]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · rw [show out.regs 15 = flagged.regs 15 from
      clearMany_reg_frame workPorts flagged 15 (by decide) (by decide)]
    change middle.regs 7 = _
    exact (embedState_register wordRegisters wordStacks (preparedWord a) small
      (Fin.castAdd_injective _ _) 7).trans hf
  · rw [show out.regs 13 = flagged.regs 13 from
      clearMany_reg_frame workPorts flagged 13 (by decide) (by decide)]
    change middle.regs 13 = _
    rw [work_register_frame _ _ _ (by decide)]
    exact prepared_register_frame_p0 _ _ (by decide) (by decide)
  · rw [show out.regs 14 = flagged.regs 14 from
      clearMany_reg_frame workPorts flagged 14 (by decide) (by decide)]
    change middle.regs 14 = _
    rw [work_register_frame _ _ _ (by decide)]
    exact prepared_register_frame_p0 _ _ (by decide) (by decide)
  · change (clearManyState workPorts flagged).stacks 22 = []
    rw [clearMany_stacks, ite_eq_right (by rw [workPorts_mem]; decide)]
    change middle.stacks 22 = []
    rw [work_stack_frame_p0 _ _ _ (by decide)]
    exact preparedWord_payload a
  · intro i hi22 hneq
    change (clearManyState workPorts flagged).stacks i = _
    rw [clearMany_stacks, ite_eq_right (by rw [workPorts_mem]; omega)]
    change middle.stacks i = _
    rw [work_stack_frame_p0 _ _ _ hi22]
    exact preparedWord_frame a i hi22 hneq

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval_oai
