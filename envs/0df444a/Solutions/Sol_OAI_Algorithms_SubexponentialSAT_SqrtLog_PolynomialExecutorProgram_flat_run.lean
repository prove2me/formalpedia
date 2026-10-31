-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:09:11.973989+00:00
-- url     : https://prove2.me/submissions/254ccc49-008c-47cd-8b5a-3b97fce5755b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S125

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

theorem physicalCfg_false_regs {l : ℕ} (pc : Option (Fin l))
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc false false false code depth operands context).regs = fun _ => false := by
  funext i
  refine Fin.addCases (m := 3) (n := 13) ?_ ?_ i
  · intro j; fin_cases j <;> rfl
  · intro j; simp [physicalCfg, reindexCfg, cfg]

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseOperandIO
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

open BitProgram StructuredCalls SubexpScanPrimitives

theorem parseRegs_injective : Function.Injective parseRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h

theorem parseStacks_injective : Function.Injective parseStacks := by decide

theorem parse_eval (d : Data) (bits tail : List Bool)
    (hin : d.stacks 27 = Encoding.frame bits ++ tail) (hscratch : d.stacks 29 = []) :
    Eval (.call parseProgram) (6 * bits.length + 4) d (afterParse d bits tail) := by
  let a : State 2 2 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ParserProgram.pair (Encoding.frame bits ++ tail) []⟩
  let b : State 2 2 :=
    ⟨ParserProgram.pair false true, ParserProgram.pair tail bits.reverse⟩
  have ha : embedState parseRegs parseStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ parseRegs_injective parseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · exact hscratch
    · intros; rfl
  have hb : embedState parseRegs parseStacks d b = afterParse d bits tail := by
    apply embedState_eq_of_ports _ _ _ _ _ parseRegs_injective parseStacks_injective
    · intro i; fin_cases i <;> simp [ parseRegs, readRegs, b, ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [parseRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [parseRegs] using h.symm⟩
      simp [ readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [ parseStacks, b, ParserProgram.pair]
    · intro i hi
      have h27 : i ≠ 27 := fun h => hi ⟨0, by simpa [parseStacks] using h.symm⟩
      have h29 : i ≠ 29 := fun h => hi ⟨1, by simpa [parseStacks] using h.symm⟩
      simp [ h27, h29]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) := by
    change Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (ParserProgram.cfg (some 0) (d.regs 0) (d.regs 1)
        (Encoding.frame bits ++ tail) [])
      (ParserProgram.cfg none false true tail bits.reverse)
    simpa only [List.append_nil] using
      ParserProgram.frame_trace bits tail [] (d.regs 0) (d.regs 1)
  simpa only [parseProgram, ha, hb] using
    eval_call_lifted ParserProgram.frameProgram parseRegs parseStacks d
      parseRegs_injective parseStacks_injective ht

theorem takeOperand_eval (d : Data) (dst : Fin 128) (bits tail : List Bool)
    (hdst : (29 : Fin 128) ≠ dst)
    (hin : d.stacks 27 = true :: (Encoding.frame bits ++ tail))
    (hscratch : d.stacks 29 = []) :
    Eval (takeOperand dst) (9 * bits.length + 8) d (takeResult d dst bits tail) := by
  have hp : Eval (.base (.atom (.pop 27 0 1))) 1 d (popped d) :=
    .base (.atom _ _)
  have hp27 : (popped d).stacks 27 = Encoding.frame bits ++ tail := by
    simp [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, hin]
  have hp29 : (popped d).stacks 29 = [] := by
    simpa [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hscratch
  have hr := parse_eval (popped d) bits tail hp27 hp29
  have ht := transfer_eval (afterParse (popped d) bits tail) 29 dst 0 1 hdst (by decide)
  have hs : ((afterParse (popped d) bits tail).stacks 29).length = bits.length := by
    simp []
  rw [hs] at ht
  have h := Eval.seq hp (Eval.seq hr ht)
  convert h using 1 <;> first | omega | rfl

theorem takeResult_stack (d : Data) (dst : Fin 128) (bits tail : List Bool)
    (hdst : dst ≠ 27) (hdst' : dst ≠ 29) :
    (takeResult d dst bits tail).stacks =
      Function.update (Function.update (Function.update d.stacks 27 tail)
        dst (bits ++ d.stacks dst)) 29 [] := by
  funext i
  by_cases h27 : i = 27 <;> by_cases h29 : i = 29 <;> by_cases hd : i = dst <;>
    simp_all [takeResult, afterTransfer, popped, StackRoutines.transferStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr
      ]

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code ExecutesIn)

theorem smallPorts_injective : Function.Injective smallPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 256 => x.val) h)

@[simp] theorem restore_self (s : Store) : restore s (s ∘ smallPorts) = s := by
  funext j
  by_cases hj : ∃ i, smallPorts i = j
  · obtain ⟨i, rfl⟩ := hj
    exact smallPorts_injective.extend_apply _ _ i
  · exact Function.extend_apply' _ _ _ hj

theorem restore_update (s : Store) (small : Fin 128 → List Bool) (i : Fin 128) (bits : List Bool) :
    restore s (Function.update small i bits) = Function.update (restore s small) (smallPorts i) bits :=
  ProgramLinking.extend_update smallPorts_injective small s i bits

theorem liftSmall_run (cmd : Cmd 16 128) (budget : ℕ) (s : Store)
    (small : Fin 128 → List Bool)
    (h : ∀ regs : Fin 16 → Bool, ∃ n rf, n ≤ budget ∧
      Eval cmd n ⟨regs, s ∘ smallPorts⟩ ⟨rf, small⟩) :
    ExecutesIn (liftSmall cmd) (budget + 1) s (restore s small) := by
  intro regs
  obtain ⟨n, rf, hn, he⟩ := h regs
  have hin : embedState id smallPorts (⟨regs, s⟩ : State 16 256)
      ⟨regs, s ∘ smallPorts⟩ = ⟨regs, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id smallPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState id smallPorts (⟨regs, s⟩ : State 16 256)
      ⟨rf, small⟩ = ⟨rf, restore s small⟩ := by
    unfold embedState restore
    simp
  have ht := eval_call_lifted (compiled cmd 0 0) id smallPorts (⟨regs, s⟩ : State 16 256)
    Function.injective_id smallPorts_injective (compiled_halt_trace he 0 0)
  exact ⟨n + 1, rf, Nat.add_le_add_right hn 1, by simpa only [hin, hout, liftSmall] using ht⟩

theorem take_run (s : Store) (bits tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame bits ++ tail))
    (h21 : s 21 = []) (h29 : s 29 = []) :
    ExecutesIn take (9 * bits.length + 9) s
      (Function.update (Function.update s 27 tail) 21 bits) := by
  have h := liftSmall_run (SubexpDenseOperandIO.takeOperand 21) (9 * bits.length + 8) s
    (Function.update (Function.update (Function.update (s ∘ smallPorts) 27 tail) 21 bits) 29 [])
    (by
      intro regs
      let a : State 16 128 := ⟨regs, s ∘ smallPorts⟩
      have ht := SubexpDenseOperandIO.takeOperand_eval a 21 bits tail (by decide) hin h29
      have hs := SubexpDenseOperandIO.takeResult_stack a 21 bits tail (by decide) (by decide)
      have ha21 : a.stacks 21 = [] := by
        simpa [a, smallPorts] using h21
      have heq : SubexpDenseOperandIO.takeResult a 21 bits tail =
          (⟨(SubexpDenseOperandIO.takeResult a 21 bits tail).regs,
            Function.update (Function.update (Function.update (s ∘ smallPorts) 27 tail) 21 bits) 29 []⟩ :
              State 16 128) := by
        apply congrArg₂ StructuredProgram.State.mk rfl
        change (SubexpDenseOperandIO.takeResult a 21 bits tail).stacks =
          Function.update (Function.update (Function.update a.stacks 27 tail) 21 bits) 29 []
        simpa [ha21] using hs
      refine ⟨_, (SubexpDenseOperandIO.takeResult a 21 bits tail).regs, le_rfl, ?_⟩
      rw [heq] at ht
      exact ht)
  simp only [restore_update, restore_self] at h
  change ExecutesIn take (9 * bits.length + 8 + 1) s
    (Function.update (Function.update (Function.update s 27 tail) 21 bits) 29 []) at h
  have heq : Function.update (Function.update (Function.update s 27 tail) 21 bits) 29 [] =
      Function.update (Function.update s 27 tail) 21 bits := by
    funext j
    by_cases hj : j = 29 <;> simp [Function.update_apply, hj, h29]
  rw [heq] at h
  exact h

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Framed arithmetic calls for source-row postfix expressions

The physical interpreter keeps its operand list on stack 27. These fixed
commands read two framed operands, call a dense polynomial service on
240/241, and frame its result from 244. All temporary stacks are restored;
the caller's remaining operands and every other stack are preserved.
-/

namespace SubexponentialSAT.SubexpRowPostfixServices

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl (Code Store Data ExecutesIn copy clear copy_run clear_run)
open SubexpDenseLiteralPadding (take take_run write reset )

theorem move_from_update (src dst : Fin 256) (s : Store) (bits : List Bool)
    (hne : src ≠ dst) (hs : src ≠ 120) (hd : (120 : Fin 256) ≠ dst)
    (hsrc : s src = []) (hdst : s dst = []) (htmp : s 120 = []) :
    ExecutesIn (move src dst) (9 * bits.length + 8)
      (Function.update s src bits) (Function.update s dst bits) := by
  let middle := Function.update (Function.update s src bits) dst bits
  have h1 : ExecutesIn (copy src dst) (7 * bits.length + 5)
      (Function.update s src bits) middle := by
    simpa [middle, hne, Ne.symm hne, hdst] using copy_run src dst (Function.update s src bits)
      hne hs hd (by simpa [Ne.symm hs] using htmp)
  have he : Function.update middle src [] = Function.update s dst bits := by
    funext j
    by_cases hj : j = src
    · subst j
      simp [middle, hne, hsrc]
    · simp [middle, Function.update_apply, hj]
  have h2 : ExecutesIn (clear src) (2 * bits.length + 3)
      middle (Function.update s dst bits) := by
    have h := clear_run src middle
    rw [he] at h
    simpa [middle, hne] using h
  simpa only [move, show 7 * bits.length + 5 + (2 * bits.length + 3) =
      9 * bits.length + 8 by omega] using h1.seq h2

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native removal of the final postfix frame. This exposes the plain
constant-coefficient-first array required by perturbation and interpolation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

theorem extract_run (s : Store) (bits : List Bool)
    (h27 : s 27 = true :: (Encoding.frame bits ++ [false])) (h28 : s 28 = [true])
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = []) (h240 : s 240 = []) :
    ExecutesIn extract (18*bits.length+27) s
      (Function.update (Function.update (Function.update s 27 []) 240 bits) 28 []) := by
  let s1 := Function.update s 27 [false]
  let s2 := Function.update s1 240 bits
  let s3 := Function.update (Function.update s 27 []) 240 bits
  have ht := SubexpDenseLiteralPadding.take_run s bits [false] h27 h21 h29
  have hm := SubexpRowPostfixServices.move_from_update 21 240 s1 bits
    (by decide) (by decide) (by decide)
    (by simp [s1,h21]) (by simp [s1,h240]) (by simp [s1,h120])
  have hc1 : ExecutesIn (clear 27) 5 s2 s3 := by
    have h := clear_run 27 s2
    have he : Function.update s2 27 [] = s3 := by
      funext i
      by_cases hi : i = 27 <;> simp [s1,s2,s3,Function.update_apply,hi]
    rw [he] at h
    simpa [s2,s1] using h
  have hc2 : ExecutesIn (clear 28) 5 s3 (Function.update s3 28 []) := by
    simpa [s3,h28] using clear_run 28 s3
  have h := ht.seq (hm.seq (hc1.seq hc2))
  convert h using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

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

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic native extraction adapter for a completed postfix interpreter. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

private theorem plainData_cfg {l : ℕ} (pc : Option (Fin l))
    (context : Fin 252 → List Bool) (code depth operands : List Bool) :
    (plainData context code depth operands).withPC pc =
      physicalCfg pc false false false code depth operands context := by
  apply congrArg₂ (Cfg.mk pc)
  · exact (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_false_regs pc code depth operands context).symm
  · rfl

private theorem extracted_context (context : Fin 252 → List Bool) (bits : List Bool) :
    Function.update (Function.update (Function.update
      (operandStore context [] [true] (Encoding.encodeList id [bits])) 27 []) 240 bits) 28 [] =
    Function.update (contextStore context) 240 bits := by
  funext i
  by_cases h27 : i = 27
  · subst i; simp [contextStore]
  by_cases h28 : i = 28
  · subst i; simp [contextStore]
  by_cases h240 : i = 240
  · subst i; simp
  by_cases h26 : i = 26
  · subst i
    simp [operandStore,contextStore]
  simp only [Function.update_apply,h27,h28,h240,ite_false]
  exact operandStore_frame context [] [true] (Encoding.encodeList id [bits]) i h26 h28 h27

theorem flatten_run {l : ℕ} (p : Program 16 256 l) {B d : ℕ} (context : Fin 252 → List Bool)
    (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
    (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
    (h240 : contextStore context 240 = [])
    (hrun : RunsIn p K
      (physicalCfg (some p.entry) false false false source [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
        (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
    ∃ rf, RunsIn (flattenProgram p) (K+18*(DensePolynomialProgram.encode out).length+28)
      (physicalCfg (some (flattenProgram p).entry) false false false source [] [] context)
      ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) := by
  obtain ⟨n,hn,ht⟩ := hrun
  let bits := DensePolynomialProgram.encode out
  let s := operandStore context [] [true] (Encoding.encodeList id [bits])
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = contextStore context i := operandStore_frame context [] [true] _ i h26 h28 h27
  have hcall : Eval (.call p) n (plainData context source [] [])
      (plainData context [] [true] (Encoding.encodeList id [bits])) := by
    apply Eval.call
    change Trace p n _ _ at ht
    simpa only [plainData_cfg,SubexpPostfixControl.operandDepth,List.length_cons,List.length_nil,
      Nat.zero_add,List.replicate_succ,List.replicate_zero,bits,Encoding.encodeList,
      id_eq] using ht
  obtain ⟨m,rf,hm,he⟩ := extract_run s bits rfl rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact h21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact h120)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact h240) (fun _ => false)
  have hfinal : Function.update (Function.update (Function.update s 27 []) 240 bits) 28 [] =
      Function.update (contextStore context) 240 bits := extracted_context context bits
  rw [hfinal] at he
  refine ⟨rf,n+m+1,by dsimp [bits] at hm; omega,?_⟩
  have h := compiled_halt_trace (hcall.seq he) 26 240
  simpa only [plainData_cfg,flattenProgram,flattenCommand,bits] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete native source interpreter returns an ordinary flat
coefficient array on240, ready for the perturbation producer. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

theorem flat_run_oai {B d : ℕ} (context : Fin 252 → List Bool)
    (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
    (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
    (h240 : contextStore context 240 = [])
    (hrun : RunsIn program K
      (physicalCfg (some program.entry) false false false source [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
        (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
    ∃ rf, RunsIn flatProgram (K+18*(DensePolynomialProgram.encode out).length+28)
      (physicalCfg (some flatProgram.entry) false false false source [] [] context)
      ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) :=
  flatten_run program context source out K h21 h120 h240 hrun

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run_oai
