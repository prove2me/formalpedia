-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:56:10.97817+00:00
-- url     : https://prove2.me/submissions/b39b477e-aea8-4930-9b74-422bcd065b5f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S104
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_ReadScalar_emit_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_add_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem key_eq_origin (n : ℕ) : key n = Squarefree.encodeIndex (Squarefree.Index.origin : Squarefree.Index (Fin n)) := by
  unfold key
  rw [Nat.add_comm n 2,List.replicate_add]
  simp [Squarefree.encodeIndex,Squarefree.Index.origin,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval (d : Machine) (src dst tmp : Fin 96)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(d.stacks src).length+5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd
    (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

theorem clear_eval (d : Machine) (src : Fin 96) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem high_injective : Function.Injective highPort := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 56+i.val = 56+j.val at hh
  omega

theorem low_ne_high (i : Fin 56) (j : Fin 40) : lowPort i ≠ highPort j := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = 56+j.val at hh
  omega

theorem update_high (low high) (i : Fin 40) (word : List Bool) :
    Function.update (tapes low high) (highPort i) word = tapes low (Function.update high i word) := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (highPort i) word) (lowPort j) =
      tapes low (Function.update high i word) (lowPort j)
    simp [low_ne_high j i]
  | right j =>
    change (Function.update (tapes low high) (highPort i) word) (highPort j) =
      tapes low (Function.update high i word) (highPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : highPort j ≠ highPort i := fun h => hj (high_injective h)
      simp [hh,hj]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native injection of a base coefficient into the first coordinate of an
extension-ring coefficient. The remaining coordinates are physically copied
from the canonical zero word. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing SubexpScanPrimitives
open IdempotentPreparationProgram

theorem scalarVector_flat {B d : ℕ} (hd : 0 < d) (zero scalar : Word B) :
    RingProgram.flat (scalarVector (d:=d) zero scalar) =
      scalar.val ++ Subexp.BlockCopyProgram.copies (d-1) zero.val := by
  simpa [scalarVector,Subexp.BlockCopyProgram.copies] using
    IdempotentProgram.flat_sparse hd scalar zero

theorem injectScalar_eval (d : Data) (dimension : ℕ) (hd : 0 < dimension)
    (hdegree : d.stacks 37=List.replicate dimension true)
    (h1 : d.stacks 1=[]) (h2 : d.stacks 2=[]) (hout : d.stacks 32=[]) :
    ∃ rf, Eval injectScalar
      (7*dimension+6+(dimension-1)*(7*(d.stacks 17).length+7)+6+
        (7*(d.stacks 31).length+5)) d
      ⟨rf,Function.update d.stacks 32
        (d.stacks 31 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ := by
  have heq : dimension-1+1=dimension := by omega
  obtain ⟨r1,hp⟩ := paddedZeros_eval d 32 1 (dimension-1)
    (by simpa [heq] using hdegree) h1 h2 (by decide) (by decide) (by decide)
  simp only [hout,List.append_nil,heq] at hp
  let a : Data := ⟨r1,Function.update d.stacks 32
    (Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩
  have hc := copy_eval a 31 32 2 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simpa [a] using h2)
  have h := hp.seq hc
  refine ⟨(afterCopy a 31 32 0 1).regs,?_⟩
  convert h using 1 <;>
    simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem]
  ; omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalarBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scalar loading uses only checked stack primitives and constant formatting.
This definition boundary keeps its correctness independent of polynomial arithmetic. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem injectPorts_injective : Function.Injective injectPorts :=
  injectPermutation.injective.comp (Fin.castAdd_injective _ _)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem read_eval (d : Machine) (word tail : List Bool)
    (hwidth : (d.stacks 12).length = word.length)
    (hsource : d.stacks 79 = word.reverse ++ tail)
    (h80 : d.stacks 80 = []) (h82 : d.stacks 82 = []) (h83 : d.stacks 83 = []) :
    Eval readScalar (11*word.length+8) d (readResult d word tail) := by
  let b := copied d 12 82
  have hcopy := copy_eval d 12 82 83 (by decide) (by decide) (by decide) h83
  have ht := ArrayPrograms.countedTransferProgram_trace (82 : Fin 96) 79 80
    (0 : Fin 8) 1 (by decide) (by decide) (by decide) (by decide)
    word.reverse tail (d.stacks 12) b.regs b.stacks
    (by simpa [b,copied,StackRoutines.copyStacks] using hsource)
    (by simp [b,copied,StackRoutines.copyStacks,h82])
    (by simpa using hwidth)
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  have hs : ArrayPrograms.countedTransferStacks (82 : Fin 96) 79 80
      word.reverse tail b.stacks = (readResult d word tail).stacks := by
    funext i
    by_cases h79 : i=79 <;> by_cases hi80 : i=80 <;> by_cases hi82 : i=82 <;>
      simp_all [ArrayPrograms.countedTransferStacks,b,copied,StackRoutines.copyStacks,
        readResult]
  have htransfer : Eval (.call (ArrayPrograms.countedTransferProgram
      (82 : Fin 96) 79 80 (0 : Fin 8) 1)) (4*word.length+3) b (readResult d word tail) := by
    apply Eval.call
    simp only [ArrayPrograms.countedTransferResult] at hh
    rw [hs] at hh
    simpa [StructuredProgram.State.withPC,readResult,b,copied,StackRoutines.readRegs_reset,
      ArrayPrograms.countedTransferProgram,Nat.add_assoc] using hh
  have h := hcopy.seq htransfer
  convert h using 1 ; simp only [hwidth] ; omega

theorem inject_eval (d : Machine) (dimension : ℕ) (hd : 0 < dimension)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (h82 : d.stacks 82=[]) (h83 : d.stacks 83=[]) (h81 : d.stacks 81=[]) :
    ∃ rf, Eval inject (injectionCost dimension (d.stacks 17).length (d.stacks 80).length) d
      ⟨rf,Function.update d.stacks 81
        (d.stacks 80 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ := by
  let a := projectState id injectPorts d
  obtain ⟨rf,ht⟩ := injectScalar_eval a dimension hd
    (by simpa [a,projectState] using hdegree)
    (by simpa [a,projectState] using h82)
    (by simpa [a,projectState] using h83)
    (by simpa [a,projectState] using h81)
  have he := eval_liftCommand_from_state injectScalar 31 32 id injectPorts d
    Function.injective_id injectPorts_injective ht
  let result : IdempotentPreparationProgram.Data :=
    ⟨rf,Function.update a.stacks 32
      (a.stacks 31 ++ Subexp.BlockCopyProgram.copies (dimension-1) (a.stacks 17))⟩
  have hb : embedState id injectPorts d result =
      (⟨rf,Function.update d.stacks 81
        (d.stacks 80 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ : Machine) := by
    apply embedState_eq_of_ports id injectPorts d _ result
      Function.injective_id injectPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i
      have hi : injectPorts i=81 ↔ i=32 := by
        rw [←injectPort_32,injectPorts_injective.eq_iff]
      simp [result,a,projectState,Function.update_apply,hi]
    · intro i hi
      have hi81 : i ≠ 81 := fun h => hi ⟨32,by simp [h]⟩
      simp [hi81]
  change Eval inject _ d (embedState id injectPorts d result) at he
  rw [hb] at he
  refine ⟨rf,?_⟩
  simpa [injectionCost,a,projectState] using he


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native
open SubexpQuarticRing

/-- The scalar loader restores every work stack. Only the consumed source
prefix and the new constant dictionary differ from the caller state. -/
theorem scalar_eval (d : Machine) (destination : Fin 96)
    (hdst : destination=61 ∨ destination=67) (dimension : ℕ) (hd : 0 < dimension)
    (word tail : List Bool)
    (hwidth : (d.stacks 12).length=word.length)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (hsource : d.stacks 79=word.reverse ++ tail)
    (hwork : ∀ i ∈ scalarWork destination, d.stacks i=[]) :
    ∃ rf, Eval (scalarConstant destination)
      (scalarCost dimension (d.stacks 17) word (d.stacks 88)) d
      ⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩ := by
  have hw70 := hwork 70 (by simp [scalarWork])
  have hw80 := hwork 80 (by simp [scalarWork])
  have hw81 := hwork 81 (by simp [scalarWork])
  have hw82 := hwork 82 (by simp [scalarWork])
  have hw83 := hwork 83 (by simp [scalarWork])
  have hw89 := hwork 89 (by simp [scalarWork])
  have hw90 := hwork 90 (by simp [scalarWork])
  have hw91 := hwork 91 (by simp [scalarWork])
  have hw92 := hwork 92 (by simp [scalarWork])
  have hwdst := hwork destination (by simp [scalarWork])
  let b := readResult d word tail
  have h1 := read_eval d word tail hwidth hsource hw80 hw82 hw83
  obtain ⟨r2,h2⟩ := inject_eval b dimension hd
    (by simpa [b,readResult] using hdegree)
    (by simpa [b,readResult] using hw82)
    (by simpa [b,readResult] using hw83)
    (by simpa [b,readResult] using hw81)
  let c : Machine := ⟨r2,Function.update b.stacks 81 (coefficient dimension (d.stacks 17) word)⟩
  change Eval inject (injectionCost dimension (d.stacks 17).length word.length) b c at h2
  let e := cleared c 80
  have h3 := clear_eval c 80
  change Eval (clear 80) (2*word.length+3) c e at h3
  let f := copied e 88 89
  have h4 := copy_eval e 88 89 70 (by decide) (by decide) (by decide)
    (by simpa [e,cleared,c,b,readResult,StackRoutines.clearStacks] using hw70)
  change Eval (copy 88 89 70) (7*(d.stacks 88).length+5) e f at h4
  obtain ⟨rf,h5⟩ := emit_eval f destination hdst (d.stacks 88)
    (coefficient dimension (d.stacks 17) word)
    (by simp [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks,hw89])
    (by simp [f,copied,e,cleared,c,StackRoutines.copyStacks,StackRoutines.clearStacks])
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw90)
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw91)
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw92)
    (by rcases hdst with rfl | rfl <;>
      simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
        StackRoutines.clearStacks] using hwdst)
  let g : Machine := ⟨rf,Function.update (Function.update (Function.update f.stacks 89 []) 81 [])
    destination (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩
  change Eval (emitConstant destination) _ f g at h5
  have hg : g =
      (⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩ : Machine) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i
    rcases hdst with rfl | rfl <;>
      by_cases hi79 : i=79 <;> by_cases hi80 : i=80 <;>
      by_cases hi81 : i=81 <;> by_cases hi89 : i=89 <;>
      simp_all [g,f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
        StackRoutines.clearStacks,Function.update_apply]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (Eval.base (StructuredProgram.Eval.skip g))))))
  change Eval (scalarConstant destination) _ d g at h
  rw [hg] at h
  exact ⟨rf,by convert h using 1 ; simp only [scalarCost] ; omega⟩

/-- The physical bytes are the standard singleton dictionary encoding. -/
theorem constantBytes_scalarVector {B dimension n : ℕ} (hd : 0 < dimension)
    (zero word : Word B) :
    constantBytes n (coefficient dimension zero.val word.val) =
      MomentsProgram.Normalize.bytes Squarefree.encodeIndex
        [(Squarefree.Index.origin (V := Fin n),scalarVector (d:=dimension) zero word)] := by
  unfold coefficient
  rw [←scalarVector_flat hd]
  simp [constantBytes,MomentsProgram.Normalize.bytes,Squarefree.Program.encodeDictionary,
    Squarefree.Program.rawEntries,HashCircuitProgram.Constant.key_eq_origin]


theorem scalarCost_words {B dimension : ℕ} (hd : 0 < dimension)
    (zero word : Word B) (shape : List Bool) :
    scalarCost dimension zero.val word.val shape = wordCost B dimension shape.length := by
  have hc : coefficient dimension zero.val word.val = RingProgram.flat (scalarVector (d:=dimension) zero word) :=
    (scalarVector_flat hd zero word).symm
  have hzlen : zero.val.length = B := zero.property
  have hwlen : word.val.length = B := word.property
  simp [scalarCost, injectionCost, hc, wordCost, hzlen, hwlen]
  ring

/-- Typed singleton bytes, with an explicit polynomial instruction count. -/
theorem scalar_words_eval {B dimension n : ℕ} (hd : 0 < dimension)
    (d : Machine) (destination : Fin 96) (hdst : destination=61 ∨ destination=67)
    (zero word : Word B) (tail : List Bool)
    (hwidth : (d.stacks 12).length=B) (hzero : d.stacks 17=zero.val)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (hshape : (d.stacks 88).length=n)
    (hsource : d.stacks 79=word.val.reverse ++ tail)
    (hwork : ∀ i ∈ scalarWork destination, d.stacks i=[]) :
    ∃ rf, Eval (scalarConstant destination) (wordCost B dimension n) d
      ⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (MomentsProgram.Normalize.bytes Squarefree.encodeIndex
          [(Squarefree.Index.origin (V := Fin n),scalarVector (d:=dimension) zero word)])⟩ := by
  obtain ⟨rf,h⟩ := scalar_eval d destination hdst dimension hd word.val tail
    (by simpa only [word.property] using hwidth) hdegree hsource hwork
  rw [hzero,scalarCost_words hd, hshape,constantBytes_scalarVector hd] at h
  exact ⟨rf,h⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native sparse arithmetic services shared by multiplier construction and Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem add_eval (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hb : high 5=Product.bytes b) (htmp : high 14=[]) :
    ∃ cost ≤ addCost c a b, ∃ rr,
      Eval add cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (plus c a b)))) := by
  simpa only [addCost, low, plus, addStored, Product.bytes, List.length_replicate] using
    IdempotentApplyProgram.add_eval p t c.modulus c.cache Squarefree.encodeIndex
      Squarefree.encodeIndex_injective (RingTriple.tableEncoding c.table)
      (List.replicate d true) c.width (List.replicate c.u true) (List.replicate c.J true)
      (by simp) c.widthLength a b regs high ha hb htmp


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
namespace Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem scalar_eval (c : Context p t n d) (hd : 0 < d) (regs : Regs) (high : Data)
    (dst : Fin 40) (hdst : dst=5 ∨ dst=11) (word : RingProgram.ScalarCode p t)
    (tail : List Bool) (hsource : high 23=word.val.reverse++tail)
    (hshape : (high 32).length=n) (hready : scalarReady dst high) :
    ∃ rr, Eval (scalarConstant (Memory.highPort dst)) (ReadScalar.wordCost (baseWidth p t) d n)
      (Memory.state regs (low c) high)
      (Memory.state rr (low c) (Function.update (Function.update high 23 tail) dst
        (Product.bytes (constant c word)))) := by
  have hwork : ∀ i ∈ ReadScalar.scalarWork (Memory.highPort dst),
      (Memory.state regs (low c) high).stacks i=[] := by
    rcases hdst with rfl | rfl <;>
      intro i hi <;>
      simp only [ReadScalar.scalarWork,List.mem_cons,List.not_mem_nil,or_false] at hi <;>
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact hready 14 (by simp) | exact hready 24 (by simp) | exact hready 25 (by simp) | exact hready 26 (by simp) | exact hready 27 (by simp) | exact hready 33 (by simp) | exact hready 34 (by simp) | exact hready 35 (by simp) | exact hready 36 (by simp) | simpa only [Memory.state,Memory.tapes_high] using hready 5 (by simp) | simpa only [Memory.state,Memory.tapes_high] using hready 11 (by simp)
  obtain ⟨rr,he⟩:=ReadScalar.scalar_words_eval hd (Memory.state regs (low c) high)
    (Memory.highPort dst) (by rcases hdst with rfl|rfl <;> decide) c.cache.zero word tail
    (by change c.width.length=baseWidth p t; exact c.widthLength)
    rfl rfl (by change (high 32).length=n; exact hshape)
    (by change high 23=word.val.reverse++tail; exact hsource) hwork
  refine ⟨rr,?_⟩
  change Eval _ _ _ ⟨rr, Function.update
    (Function.update (Memory.tapes (low c) high) (Memory.highPort 23) tail)
    (Memory.highPort dst) (Product.bytes (constant c word))⟩ at he
  simpa only [Memory.update_high,Memory.state] using he

/-- The constant term is read from the real reversed coefficient stream. -/
theorem add_constant_eval_oai (c : Context p t n d) (hd : 0 < d)
    (a : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (word : RingProgram.ScalarCode p t)
    (regs : Regs) (high : Data) (tail : List Bool)
    (ha : high 11=Product.bytes a) (hsource : high 23=word.val.reverse++tail)
    (hshape : (high 32).length=n) (hready : scalarReady 5 high) :
    ∃ cost ≤ ReadScalar.wordCost (baseWidth p t) d n+addCost c a (constant c word), ∃ rr,
      Eval (.seq (scalarConstant 61) add) cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update (Function.update high 23 tail) 11
          (Product.bytes (plus c a (constant c word))))) := by
  obtain ⟨r1,hs⟩:=scalar_eval c hd regs high 5 (Or.inl rfl) word tail hsource hshape hready
  let next:=Function.update (Function.update high (23:Fin 40) tail) 5
    (Product.bytes (constant c word))
  obtain ⟨cost,hcost,rr,he⟩:=add_eval c a (constant c word) r1 next
    (by simpa [next] using ha) (by simp [next])
    (by simpa [next] using hready 14 (by simp))
  have h5 : high 5=[]:=hready 5 (by simp)
  have hb : binaryResult next (Product.bytes (plus c a (constant c word)))=
      Function.update (Function.update high 23 tail) 11
        (Product.bytes (plus c a (constant c word))) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=5 <;> by_cases hk : i=23 <;>
      simp_all [binaryResult,next]
  rw [hb] at he
  exact ⟨_,Nat.add_le_add_left hcost _,rr,hs.seq he⟩

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram


/-! Complete native evaluation of one degree-two coefficient digit. -/


/-! The native Horner accumulator update, including every move and cleanup. -/


/-! Measured descending Horner loop over the actual computed coefficient tape. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval_oai
