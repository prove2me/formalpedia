-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:58:51.750859+00:00
-- url     : https://prove2.me/submissions/22802736-840c-4d48-b71e-a93fce98c35e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S104
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_ReadScalar_emit_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_accumulator_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_add_constant_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_mul_hash_clean

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing


theorem descendingTape_cons {B : ℕ} (v : Triple (Word B)) (vs : List (Triple (Word B))) :
    descendingTape (v::vs)=v.c.val.reverse++(v.b.val.reverse++(v.a.val.reverse++descendingTape vs)) := by
  simp [descendingTape,List.append_assoc]

theorem descendingTape_length {B : ℕ} (vs : List (Triple (Word B))) :
    (descendingTape vs).length=3*B*vs.length := by
  induction vs with
  | nil => simp [descendingTape]
  | cons v vs ih =>
    rw [descendingTape_cons]
    simp only [List.length_append,List.length_reverse, v.a.property,v.b.property,v.c.property,List.length_cons,ih,Nat.mul_add,Nat.mul_one]
    omega

theorem descendingTape_cons_ne_nil {B : ℕ} (hB : 0 < B)
    (v : Triple (Word B)) (vs : List (Triple (Word B))) : descendingTape (v::vs)≠[] := by
  intro h
  have he:=congrArg List.length h
  rw [descendingTape_length] at he
  simp only [List.length_cons,List.length_nil] at he
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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


theorem seq_tail {r s : ℕ} {a b c : Cmd r s} {n m : ℕ} {x y z : State r s}
    (hab : Eval (.seq a b) n x y) (hc : Eval c m y z) :
    Eval (.seq a (.seq b c)) (n+m) x z := by
  cases hab with
  | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram


/-! Complete native evaluation of one degree-two coefficient digit. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem quadratic_eval (ctx : Context p t n d) (hd : 0 < d)
    (h : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t))
    (regs : Regs) (high : Data) (tail : List Bool)
    (hh : high 12=Product.bytes h) (hempty : high 5=[])
    (hsource : high 23=v.c.val.reverse++(v.b.val.reverse++(v.a.val.reverse++tail)))
    (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
    ∃ cost ≤ quadraticCost ctx h v, ∃ rr,
      Eval tripleStep cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update (Function.update high 23 tail) 11
          (Product.bytes (tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v)))) := by
  let t1:=v.b.val.reverse++(v.a.val.reverse++tail)
  let t2:=v.a.val.reverse++tail
  let c:=constant ctx v.c
  let ch:=mul ctx c h
  let chb:=plus ctx ch (constant ctx v.b)
  let chbh:=mul ctx chb h
  let out:=plus ctx chbh (constant ctx v.a)
  let h1:=Function.update (Function.update high (23:Fin 40) t1) 11 (Product.bytes c)
  obtain ⟨r1,e1⟩:=scalar_eval ctx hd regs high 11 (Or.inr rfl) v.c t1 hsource hshape hready
  change Eval (scalarConstant 67) _ _ (Memory.state r1 (low ctx) h1) at e1
  obtain ⟨k2,b2,r2,e2⟩:=mul_hash_clean ctx c h r1 h1
    (by simp [h1]) (by simpa [h1] using hh)
    (by simpa [h1] using hempty) (by simpa [h1] using hready 14 (by simp))
  let h2:=Function.update h1 (11:Fin 40) (Product.bytes ch)
  change Eval _ _ _ (Memory.state r2 (low ctx) h2) at e2
  have ready2 : scalarReady 5 h2 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h2,h1,hempty,hready]
  obtain ⟨k3,b3,r3,e3⟩:=add_constant_eval ctx hd ch v.b r2 h2 t2
    (by simp [h2]) (by simp [h2,h1,t1,t2])
    (by simpa [h2,h1] using hshape) ready2
  let h3:=Function.update (Function.update h2 (23:Fin 40) t2) 11 (Product.bytes chb)
  change Eval _ _ _ (Memory.state r3 (low ctx) h3) at e3
  obtain ⟨k4,b4,r4,e4⟩:=mul_hash_clean ctx chb h r3 h3
    (by simp [h3]) (by simpa [h3,h2,h1] using hh)
    (by simpa [h3,h2,h1] using hempty)
    (by simpa [h3,h2,h1] using hready 14 (by simp))
  let h4:=Function.update h3 (11:Fin 40) (Product.bytes chbh)
  change Eval _ _ _ (Memory.state r4 (low ctx) h4) at e4
  have ready4 : scalarReady 5 h4 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h4,h3,h2,h1,hempty,hready]
  obtain ⟨k5,b5,r5,e5⟩:=add_constant_eval ctx hd chbh v.a r4 h4 tail
    (by simp [h4]) (by simp [h4,h3,t2])
    (by simpa [h4,h3,h2,h1] using hshape) ready4
  let h5:=Function.update (Function.update h4 (23:Fin 40) tail) 11 (Product.bytes out)
  change Eval _ _ _ (Memory.state r5 (low ctx) h5) at e5
  have he:=e1.seq (seq_tail e2 (seq_tail e3 (seq_tail e4 (seq_tail e5
    (Eval.base (StructuredProgram.Eval.skip (Memory.state r5 (low ctx) h5)))))))
  have hh5 : h5=Function.update (Function.update high 23 tail) 11 (Product.bytes out) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=23 <;>
      simp_all [h5,h4,h3,h2,h1]
  rw [hh5] at he
  refine ⟨ReadScalar.wordCost (baseWidth p t) d n+(k2+(k3+(k4+(k5+0)))),?_,r5,?_⟩
  · dsimp [quadraticCost,c,ch,chb,chbh] at *
    omega
  · exact he

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! The native Horner accumulator update, including every move and cleanup. -/


/-! Measured descending Horner loop over the actual computed coefficient tape. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem peek_eval (regs : Regs) (l : Fin 56 → List Bool) (high : Data) :
    Eval peekCoefficients 1 (Memory.state regs l high)
      (Memory.state (readRegs regs 0 7 (high 23).head?) l high) := by
  exact .base (.atom _ _)

theorem loop_eval_oai (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
    (ha : high 31=Product.bytes a) (h5 : high 5=[]) (h29 : high 29=[])
    (hsource : high 23=descendingTape vs)
    (hshape : (high 32).length=n) (hready : scalarReady 11 high)
    (htest : regs 7=(high 23).head?.isSome) :
    ∃ cost ≤ loopCost ctx h g vs a, ∃ rr,
      Eval (.while 7 hornerStep) cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update (Function.update high 23 []) 31
          (Product.bytes (loopResult ctx h g vs a)))) := by
  induction vs generalizing regs high a with
  | nil =>
    have hs : high 23=[]:=hsource
    have ht : regs 7=false:=by simpa [hs] using htest
    have heq : Function.update (Function.update high 23 []) 31 (Product.bytes a)=high := by
      funext i
      by_cases hi : i=23 <;> by_cases hj : i=31 <;> simp_all
    refine ⟨1,by simp [loopCost],regs,?_⟩
    simpa only [loopResult,heq] using (Eval.while_false (a:=Memory.state regs (low ctx) high) (body:=hornerStep) ht)
  | cons v vs ih =>
    let e:=tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
    let next:=plus ctx (mul ctx a g) e
    let hq:=Function.update (Function.update high (23:Fin 40) (descendingTape vs)) 11 (Product.bytes e)
    obtain ⟨kq,bq,rq,eq⟩:=quadratic_eval ctx hd h v regs high (descendingTape vs) hh h5
      (by simpa only [descendingTape_cons] using hsource) hshape hready
    change Eval tripleStep kq _ (Memory.state rq (low ctx) hq) at eq
    obtain ⟨ka,ba,ra,ea⟩:=accumulator_eval ctx e a g rq hq
      (by simp [hq]) (by simpa [hq] using ha) (by simpa [hq] using hg)
      (by simpa [hq] using h5) (by simpa [hq] using h29)
      (by simpa [hq] using hready 14 (by simp))
    let hr:=Function.update (Function.update hq (11:Fin 40) []) 31 (Product.bytes next)
    change Eval accumulatorStep ka _ (Memory.state ra (low ctx) hr) at ea
    let rp:=readRegs ra 0 7 (hr 23).head?
    have ep:=peek_eval ra (low ctx) hr
    have rready : scalarReady 11 hr := by
      simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
      intro i hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [hr,hq,hready]
    obtain ⟨kl,bl,rl,el⟩:=ih next rp hr
      (by simpa [hr,hq] using hh) (by simpa [hr,hq] using hg) (by simp [hr])
      (by simpa [hr,hq] using h5) (by simpa [hr,hq] using h29)
      (by simp [hr,hq]) (by simpa [hr,hq] using hshape) rready
      (by simp [rp,readRegs])
    have test : regs 7=true := by
      rw [htest,hsource]
      cases htape : descendingTape (v::vs) with
      | nil => exact False.elim ((descendingTape_cons_ne_nil hB v vs) htape)
      | cons b bs => rfl
    have hb : Eval hornerStep (kq+(ka+1)) (Memory.state regs (low ctx) high)
        (Memory.state rp (low ctx) hr) := eq.seq (ea.seq ep)
    have he:=Eval.while_true test hb el
    have hout : Function.update (Function.update hr 23 []) 31
        (Product.bytes (loopResult ctx h g vs next))=
        Function.update (Function.update high 23 []) 31
          (Product.bytes (loopResult ctx h g (v::vs) a)) := by
      funext i
      have hz : high 11=[]:=hready 11 (by simp)
      by_cases hi : i=11 <;> by_cases hj : i=23 <;> by_cases hk : i=31 <;>
        simp_all [hr,hq,loopResult,next,e,Function.update_apply]
    rw [hout] at he
    refine ⟨kq+(ka+1)+kl+1,?_,rl,he⟩
    dsimp only [next,e] at bl ba
    dsimp only [loopCost]
    omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval_oai
