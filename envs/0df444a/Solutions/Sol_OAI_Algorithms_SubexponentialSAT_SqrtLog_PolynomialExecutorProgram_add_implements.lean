-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:28:54.485033+00:00
-- url     : https://prove2.me/submissions/a99d21b9-6355-4c87-8f16-245fc1167e66

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Fixed_add_spec
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpRowPostfixServices_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Small, extensional frame facts for the row interpreter. These proofs
split only its four control ports; they never enumerate the 256-stack frame. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram StructuredCalls
open SubexpPostfixGlobal (reindexCfg)
open SubexpPostfixInterpreter (cfg)

theorem physicalCfg_frame {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool)
    (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    (physicalCfg pc v p op code depth operands context).stacks i = contextStore context i := by
  obtain ⟨j, rfl⟩ := ports.surjective i
  revert h26 h28 h27
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k
    · intro h _ _; exact False.elim (h ports_zero)
    · intro _ h _; exact False.elim (h ports_one)
    · intro _ _ h; exact False.elim (h ports_two)
    · intro _ _ _
      simp [physicalCfg, contextStore, reindexCfg, cfg, Fin.addCases,
        SubexpPostfixControl.quadruple]
  · intro k _ _ _
    simp [physicalCfg, contextStore, reindexCfg, cfg]

private theorem local_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (cfg (r := 13) pc v p op code depth new context).stacks =
      Function.update (cfg (r := 13) pc v p op code depth old context).stacks
        (2 : Fin 256) new := by
  funext i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ i
  · intro j
    fin_cases j <;> rfl
  · intro j
    have hj : Fin.natAdd 4 j ≠ (2 : Fin 256) := by
      intro h
      have hv := congrArg Fin.val h
      change 4 + j.val = 2 at hv
      omega
    simp [cfg, hj]

theorem physicalCfg_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth new context).stacks =
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new := by
  funext i
  have hi : ports.symm i = (2 : Fin 256) ↔ i = 27 := by
    constructor
    · intro h
      have hh := congrArg ports h
      simpa only [Equiv.apply_symm_apply, ports_two] using hh
    · intro h
      subst i
      exact ports_symm_27
  change (cfg (r := 13) pc v p op code depth new context).stacks (ports.symm i) = _
  rw [local_update pc v p op code depth old new context]
  simp only [Function.update_apply, hi, physicalCfg, reindexCfg]

theorem physicalCfg_false_regs {l : ℕ} (pc : Option (Fin l))
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc false false false code depth operands context).regs = fun _ => false := by
  funext i
  refine Fin.addCases (m := 3) (n := 13) ?_ ?_ i
  · intro j; fin_cases j <;> rfl
  · intro j; simp [physicalCfg, reindexCfg, cfg]

/-- The framed service endpoint is exactly the interpreter's next boundary. -/
theorem physicalCfg_after {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    ((⟨fun _ => false,
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new⟩ :
      State 16 256).withPC (l := l) none) =
      physicalCfg (l := l) none false false false code depth new context := by
  have hs := physicalCfg_update pc v p op code depth old new context
  have hregs := physicalCfg_false_regs (l := l) none code depth new context
  apply congrArg₂ (Cfg.mk none)
  · exact hregs.symm
  · exact hs.symm

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stored arithmetic data for the row interpreter. Readiness is stated on
the fixed context alone, and proved invariant when source, operand, and
temporary argument ports change. No arithmetic trace is assumed here. -/

namespace SubexponentialSAT.SubexpRowPostfixContext

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Store bufferPorts)
open SubexpRowPostfixInterpreter (physicalCfg contextStore)

theorem operandStore_frame (context : Fin 252 → List Bool)
    (code depth operands : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    operandStore context code depth operands i = contextStore context i :=
  SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27

theorem preparedStore_frame (context : Fin 252 → List Bool)
    (code depth operands left right tail : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) (h240 : i ≠ 240) (h241 : i ≠ 241) :
    preparedStore context code depth operands left right tail i = contextStore context i := by
  simp only [preparedStore, SubexpRowPostfixServices.prepared, Function.update_apply,
    h240, h241, h27, ite_false]
  exact operandStore_frame context code depth operands i h26 h28 h27

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Persistent native arithmetic context for the source-row postfix machine.
The dispatcher owns26/27/28; neither coefficient-array service touches them. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (contextStore physicalCfg)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore operandStore_frame preparedStore_frame)

variable {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d)}
    {table : Fin d → Fin d → Fin d → Word (baseWidth p t)} {J : ℕ}
    {width : List Bool} {frame : Fin 6 → List Bool} {context : Fin 252 → List Bool}

/-- The native metadata is invariant under source, operand-stack, and binary
argument changes. This is stronger than the shared all-low-ports frame. -/
theorem Ready.prepared_arithmetic (H : Ready p t M cache ops table J width frame context)
    (code depth operands left right tail : List Bool) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (preparedStore context code depth operands left right tail) width frame := by
  constructor
  · intro i h8 h9
    rw [preparedStore_frame]
    · exact H.arithmetic.high i h8 h9
    all_goals fin_cases i <;> decide
  · intro i
    rw [preparedStore_frame]
    · exact H.arithmetic.low i
    all_goals
      intro h
      have hv := congrArg Fin.val h
      change i.val = _ at hv
      have hi := i.isLt
      omega
  · rw [preparedStore_frame _ _ _ _ _ _ _ 104 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.width
  · exact H.arithmetic.scalarWidthLength
  · rw [preparedStore_frame _ _ _ _ _ _ _ 204 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.degreeLength
  · rw [preparedStore_frame _ _ _ _ _ _ _ 120 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.scratch
  · intro i hlo hhi
    rw [preparedStore_frame]
    · exact H.arithmetic.work i hlo hhi
    all_goals intro he; have hv := congrArg Fin.val he; norm_num at hv; omega

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native literal loading and padding for coefficient-array postfix source. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

theorem update_run {l : ℕ} (service : Program 16 256 l) (K : ℕ)
    (v p op : Bool) (code depth old new : List Bool) (context : Fin 252 → List Bool)
    (h : RunsIn service K
      ((⟨(physicalCfg (some service.entry) v p op code depth old context).regs,
        operandStore context code depth old⟩ : State 16 256).withPC (some service.entry))
      ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
        State 16 256).withPC none)) :
    RunsIn service K (physicalCfg (some service.entry) v p op code depth old context)
      (physicalCfg none false false false code depth new context) := by
  have he : ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
      State 16 256).withPC none) = physicalCfg none false false false code depth new context :=
    SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_after (some service.entry) v p op
      code depth old new context
  rw [he] at h
  exact h


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native add, truncated multiply and padding services for the
source-row postfix interpreter on arbitrary-degree coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore operandStore_frame preparedStore_frame)

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem add_implements_oai (hB : 0 < baseWidth p t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1) :
    ImplementsOnGlobal (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
      DensePolynomialProgram.encode (addValue ops) false addProgram
      (fun _ _ => binaryBound (DensePolynomialProgram.AddService.budget d (baseWidth p t) J J)
        (J*(d*baseWidth p t))) context := by
  intro P Q hP hQ xs code depth
  let operands := Encoding.encodeList DensePolynomialProgram.encode (Q :: P :: xs)
  let tail := Encoding.encodeList DensePolynomialProgram.encode xs
  let s := operandStore context code depth operands
  let sp := preparedStore context code depth operands
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    operandStore_frame context code depth operands i h26 h28 h27
  have harith := DensePolynomialProgram.Fixed.add_spec p t M cache ops table hB hadd sp J width frame
    (H.prepared_arithmetic code depth operands _ _ tail)
  have hr := harith sp ⟨P,hP⟩ ⟨Q,hQ⟩ (CRTLocalProgram.lowFrame_refl sp)
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,operandStore_frame,
      H.empty244])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,operandStore_frame,
      H.empty245])
  apply update_run _ _ true true false code depth operands
    (Encoding.encodeList DensePolynomialProgram.encode (addValue ops P Q :: xs)) context
  have h := SubexpRowPostfixServices.program_runsIn DensePolynomialProgram.AddService.command
    (DensePolynomialProgram.AddService.budget d (baseWidth p t) J J) s
    (physicalCfg (some addProgram.entry) true true false code depth operands context).regs
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
    (DensePolynomialProgram.encode (addValue ops P Q)) rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.arithmetic.scratch)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact H.empty240)
    (by rw [hs 241 (by decide) (by decide) (by decide)]; exact H.empty241)
    (by rw [hs 244 (by decide) (by decide) (by decide)]; exact H.empty244) hr
  have hlen : (addValue ops P Q).length = J := by
    unfold addValue
    rw [SubexpPolynomialAddService.addProgram_length,hP,hQ,Nat.max_self]
  simpa [addProgram,binaryBound,DensePolynomialProgram.encode_length,hP,hQ,hlen,
    s, operands, tail, Encoding.encodeList] using h


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements_oai
