-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:11:49.77466+00:00
-- url     : https://prove2.me/submissions/290ca1eb-4dfb-4a22-97d6-a52cd2524672

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

theorem resetList_eval (is : List (Fin 16)) (d : StructuredProgram.State 16 128) :
    StructuredProgram.Eval (resetList is) is.length d (resetData is d) := by
  induction is generalizing d with
  | nil => simpa [resetList, resetData] using StructuredProgram.Eval.skip d
  | cons i is ih =>
      have h := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set i false) d)
        (ih ((StructuredProgram.Atom.set i false).eval d))
      have hd : resetData is ((StructuredProgram.Atom.set i false).eval d) = resetData (i :: is) d := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = i <;> by_cases hm : j ∈ is <;>
            simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg,
              execInstr, Function.update, hj, hm]
        · rfl
      simpa only [resetList, List.length_cons, hd, Nat.add_comm] using h

theorem reset_trace (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool) :
    Trace resetProgram 17 ⟨some resetProgram.entry, regs, stk⟩ ⟨none, fun _ => false, stk⟩ := by
  have h := resetList_eval (List.finRange 16) ⟨regs, stk⟩
  have he : StructuredProgram.Eval (resetList (List.finRange 16)) 16
      ⟨regs, stk⟩ ⟨fun _ => false, stk⟩ := by
    simpa [resetData] using h
  exact StructuredProgram.compiled_halt_trace he 26 15

end SubexponentialSAT.SubexpEvaluationProgram

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

theorem writeRegs_injective : Function.Injective writeRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h
theorem writeStacks_injective : Function.Injective writeStacks := by decide

theorem write_eval (d : Data) (bits : List Bool) (hscratch : d.stacks 29 = bits.reverse) :
    Eval (.call writeProgram) (5 * bits.length + 7) d (afterWrite d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 26) (d.stacks 28) (d.stacks 27) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 26) (d.stacks 28) (true :: (Encoding.frame bits ++ d.stacks 27)) []
  have ha : embedState writeRegs writeStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ writeRegs_injective writeStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> first | rfl | exact hscratch
    · intros; rfl
  have hb : embedState writeRegs writeStacks d b = afterWrite d bits := by
    apply embedState_eq_of_ports _ _ _ _ _ writeRegs_injective writeStacks_injective
    · intro i; fin_cases i <;>
        simp [afterWrite, writeRegs, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [writeRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [writeRegs] using h.symm⟩
      simp [afterWrite,h0,h1]
    · intro i; fin_cases i <;>
        simp [afterWrite, writeStacks, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple]
    · intro i hi
      have h27 : i ≠ 27 := fun h => hi ⟨2, by simpa [writeStacks] using h.symm⟩
      have h29 : i ≠ 29 := fun h => hi ⟨3, by simpa [writeStacks] using h.symm⟩
      simp [afterWrite,h27,h29]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 26) (d.stacks 28)
    (d.stacks 27) (d.regs 0) (d.regs 1) (d.regs 2)
  simpa only [writeProgram, ha, hb] using
    eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writeRegs writeStacks d
      writeRegs_injective writeStacks_injective (a := a) (b := b) ht

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

theorem padding_exit_any (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3 (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, operandStacks, Function.update_apply]

theorem padding_trace_any (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none rf [] (input.drop shape.length) ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
      refine ⟨readRegs regs 1 3 none, ?_⟩
      simpa [padTo] using padding_exit_any regs input output
  | cons bit shape ih =>
      obtain ⟨rf, ht⟩ := ih (paddingRegs regs bit input) input.tail
        (input.head?.getD false :: output)
      refine ⟨rf, ?_⟩
      have h := (padding_round regs bit shape input output).trans ht
      cases input <;> convert h using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] <;> omega

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

theorem padRegs_injective : Function.Injective padRegs := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)
theorem padPorts_injective : Function.Injective padPorts := by decide

theorem pad_run (s : Store) (shape bits : List Bool)
    (h99 : s 99 = shape) (h21 : s 21 = bits) (h29 : s 29 = []) :
    ExecutesIn pad (4 * shape.length + 3) s
      (Function.update (Function.update (Function.update s 99 []) 21 (bits.drop shape.length))
        29 (padTo shape bits).reverse) := by
  intro regs
  obtain ⟨rf, ht⟩ := padding_trace_any (regs ∘ padRegs) shape bits []
  let a : State 8 3 := ⟨regs ∘ padRegs, operandStacks shape bits []⟩
  let b : State 8 3 := ⟨rf, operandStacks [] (bits.drop shape.length) (padTo shape bits).reverse⟩
  have hin : embedState padRegs padPorts (⟨regs, s⟩ : State 16 256) a = ⟨regs, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ padRegs_injective padPorts_injective
    · intros; rfl
    · intros; rfl
    · intro j; fin_cases j <;> simp [a, padPorts, operandStacks, h99, h21, h29]
    · intros; rfl
  let out := Function.update (Function.update (Function.update s 99 []) 21 (bits.drop shape.length))
    29 (padTo shape bits).reverse
  let rr := Function.extend padRegs rf regs
  have hout : embedState padRegs padPorts (⟨regs, s⟩ : State 16 256) b = ⟨rr, out⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ padRegs_injective padPorts_injective
    · intro j; exact padRegs_injective.extend_apply rf regs j
    · intro j hj; exact Function.extend_apply' _ _ _ hj
    · intro j; fin_cases j <;> simp [out, b, padPorts, operandStacks]
    · intro j hj
      have h99' : j ≠ 99 := fun h => hj ⟨0, h.symm⟩
      have h21' : j ≠ 21 := fun h => hj ⟨1, h.symm⟩
      have h29' : j ≠ 29 := fun h => hj ⟨2, h.symm⟩
      simp [out, h99', h21', h29']
  have ht' : Trace paddingProgram (4 * shape.length + 3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := by
    simpa [a, b, paddingCfg, StructuredProgram.State.withPC] using ht
  have he := eval_call_lifted paddingProgram padRegs padPorts (⟨regs, s⟩ : State 16 256)
    padRegs_injective padPorts_injective ht'
  exact ⟨_, rr, le_rfl, by simpa only [hin, hout, pad] using he⟩

theorem write_run (s : Store) (bits : List Bool) (h29 : s 29 = bits.reverse) :
    ExecutesIn write (5 * bits.length + 8) s
      (Function.update (Function.update s 27 (true :: (Encoding.frame bits ++ s 27))) 29 []) := by
  have h := liftSmall_run (.call SubexpDenseOperandIO.writeProgram) (5 * bits.length + 7) s
    (Function.update (Function.update (s ∘ smallPorts) 27 (true :: (Encoding.frame bits ++ s 27))) 29 [])
    (by
      intro regs
      let a : State 16 128 := ⟨regs, s ∘ smallPorts⟩
      have ht := SubexpDenseOperandIO.write_eval a bits h29
      exact ⟨_, (SubexpDenseOperandIO.afterWrite a bits).regs, le_rfl, ht⟩)
  simp only [restore_update, restore_self] at h
  change ExecutesIn write (5 * bits.length + 7 + 1) s
    (Function.update (Function.update s 27 (true :: (Encoding.frame bits ++ s 27))) 29 []) at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl

/-- The complete actual loader replaces the top literal with exactly the
cached width, preserving every other stack and restoring all work buffers. -/
theorem command_run (s : Store) (bits tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame bits ++ tail))
    (h21 : s 21 = []) (h29 : s 29 = []) (h99 : s 99 = []) (h120 : s 120 = []) :
    ExecutesIn command (12 * bits.length + 16 * (s 242).length + 28) s
      (Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail))) := by
  let s1 := Function.update (Function.update s 27 tail) 21 bits
  let s2 := Function.update s1 99 (s 242)
  let s3 := Function.update (Function.update (Function.update s2 99 []) 21 (bits.drop (s 242).length))
    29 (padTo (s 242) bits).reverse
  let s4 := Function.update s3 21 []
  have h1 := take_run s bits tail hin h21 h29
  have h2 : ExecutesIn (SubexpConvolutionControl.copy 242 99) (7 * (s 242).length + 5) s1 s2 := by
    simpa [s1, s2, h99] using SubexpConvolutionControl.copy_run 242 99 s1
      (by decide) (by decide) (by decide) (by simp [s1, h120])
  have h3 := pad_run s2 (s 242) bits (by simp [s2]) (by simp [s2, s1]) (by simp [s2, s1, h29])
  have h4 := SubexpConvolutionControl.clear_run 21 s3
  have h5 := write_run s4 (padTo (s 242) bits) (by simp [s4, s3])
  have he : Function.update (Function.update s4 27
      (true :: (Encoding.frame (padTo (s 242) bits) ++ s4 27))) 29 [] =
      Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail)) := by
    funext j
    by_cases h27 : j = 27 <;> by_cases hj21 : j = 21 <;>
      by_cases hj29 : j = 29 <;> by_cases hj99 : j = 99 <;>
      simp_all [s4, s3, s2, s1]
  rw [he] at h5
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  simp [s3, s2, s1, List.length_drop, padTo_length]
  omega

theorem reset_eval (regs : Fin 16 → Bool) (s : Store) :
    Eval reset 17 (⟨regs, s⟩ : State 16 256) ⟨fun _ => false, s⟩ := by
  let a : State 16 128 := ⟨regs, s ∘ smallPorts⟩
  let b : State 16 128 := ⟨fun _ => false, s ∘ smallPorts⟩
  have hin : embedState id smallPorts (⟨regs, s⟩ : State 16 256) a = ⟨regs, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id smallPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState id smallPorts (⟨regs, s⟩ : State 16 256) b = ⟨fun _ => false, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id smallPorts_injective
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intros; rfl
    · intros; rfl
  have ht : Trace SubexpEvaluationProgram.resetProgram 17
      (a.withPC (some SubexpEvaluationProgram.resetProgram.entry)) (b.withPC none) :=
    SubexpEvaluationProgram.reset_trace regs (s ∘ smallPorts)
  have he := eval_call_lifted SubexpEvaluationProgram.resetProgram id smallPorts
    (⟨regs, s⟩ : State 16 256) Function.injective_id smallPorts_injective ht
  simpa only [hin, hout, reset] using he

/-- A fixed byte loader for arbitrary raw literal payloads, including short
constants and X. Its terminal registers and work buffers are all restored. -/
theorem program_runsIn_oai (s : Store) (regs : Fin 16 → Bool) (bits tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame bits ++ tail))
    (h21 : s 21 = []) (h29 : s 29 = []) (h99 : s 99 = []) (h120 : s 120 = []) :
    RunsIn program (12 * bits.length + 16 * (s 242).length + 46)
      ((⟨regs, s⟩ : State 16 256).withPC (some program.entry))
      ((⟨fun _ => false,
        Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail))⟩ :
          State 16 256).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := command_run s bits tail hin h21 h29 h99 h120 regs
  have hr := reset_eval rf
    (Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail)))
  exact ⟨n + 17 + 1, by omega, compiled_halt_trace (he.seq hr) 27 27⟩

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn_oai
