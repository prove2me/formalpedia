-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:13:47.27382+00:00
-- url     : https://prove2.me/submissions/27376d15-01bd-471a-ac9e-8a6ceea7a9f5

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
open SubexpDenseLiteralPadding (take take_run write write_run reset reset_eval)

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

theorem prepare_run (s : Store) (left right tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame right ++
      (true :: (Encoding.frame left ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) :
    ExecutesIn prepare (18 * (left.length + right.length) + 34) s
      (prepared s left right tail) := by
  let rest := true :: (Encoding.frame left ++ tail)
  let s1 := Function.update s 27 rest
  let s2 := Function.update s1 241 right
  let s3 := Function.update s2 27 tail
  have h1 := take_run s right rest hin h21 h29
  have h2 := move_from_update 21 241 s1 right (by decide) (by decide) (by decide)
    (by simpa [s1] using h21) (by simpa [s1] using h241) (by simpa [s1] using h120)
  have h3 := take_run s2 left tail (by simp [s2, s1, rest])
    (by simpa [s2, s1] using h21) (by simpa [s2, s1] using h29)
  have h4 := move_from_update 21 240 s3 left (by decide) (by decide) (by decide)
    (by simpa [s3, s2, s1] using h21) (by simpa [s3, s2, s1] using h240)
    (by simpa [s3, s2, s1] using h120)
  have he : Function.update s3 240 left = prepared s left right tail := by
    funext j
    by_cases hj : j = 27 <;> simp [s3, s2, s1, prepared, Function.update_apply, hj]
  rw [he] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | rfl | omega

theorem finish_run (s : Store) (left right tail out : List Bool)
    (h29 : s 29 = []) (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = []) :
    ExecutesIn finish (2 * (left.length + right.length) + 8 * out.length + 17)
      (Function.update (prepared s left right tail) 244 out)
      (Function.update s 27 (true :: (Encoding.frame out ++ tail))) := by
  let base := Function.update s 27 tail
  let s1 := Function.update (Function.update base 241 right) 244 out
  let s2 := Function.update base 244 out
  let s3 := Function.update base 29 out.reverse
  have he1 : Function.update (Function.update (prepared s left right tail) 244 out)
      240 [] = s1 := by
    funext j
    by_cases hj : j = 240 <;>
      simp [prepared, s1, base, Function.update_apply, hj, h240]
  have h1 : ExecutesIn (clear 240) (2 * left.length + 3)
      (Function.update (prepared s left right tail) 244 out) s1 := by
    have h := clear_run 240 (Function.update (prepared s left right tail) 244 out)
    rw [he1] at h
    simpa [prepared] using h
  have he2 : Function.update s1 241 [] = s2 := by
    funext j
    by_cases hj : j = 241 <;> simp [s1, s2, base, Function.update_apply, hj, h241]
  have h2 : ExecutesIn (clear 241) (2 * right.length + 3) s1 s2 := by
    have h := clear_run 241 s1
    rw [he2] at h
    simpa [s1] using h
  have he3 : Function.update (Function.update s2 244 []) 29
      ((s2 244).reverse ++ s2 29) = s3 := by
    funext j
    by_cases hj : j = 244 <;> simp [s3, s2, base, Function.update_apply, hj, h29, h244]
  have h3 : ExecutesIn (SubexpPolynomialServiceControl.transfer 244 29)
      (3 * out.length + 3) s2 s3 := by
    have h := SubexpPolynomialServiceControl.transfer_run 244 29 s2 (by decide)
    rw [he3] at h
    simpa [s2] using h
  have he4 : Function.update (Function.update s3 27
      (true :: (Encoding.frame out ++ s3 27))) 29 [] =
      Function.update s 27 (true :: (Encoding.frame out ++ tail)) := by
    funext j
    by_cases hj : j = 29 <;> by_cases hj27 : j = 27 <;>
      simp [s3, base, hj, hj27, h29]
  have h4 := write_run s3 out (by simp [s3])
  rw [he4] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | rfl | omega

/-- Exact framing around any checked dense-array arithmetic service.
The service hypothesis is a trace of the inserted command on the actual
prepared stores, and is later discharged by the concrete add/multiply tables. -/
theorem program_runsIn_oai (arithmetic : Code) (K : ℕ) (s : Store)
    (regs : Fin 16 → Bool) (left right tail out : List Bool)
    (hin : s 27 = true :: (Encoding.frame right ++
      (true :: (Encoding.frame left ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (harithmetic : ExecutesIn arithmetic K (prepared s left right tail)
      (Function.update (prepared s left right tail) 244 out)) :
    RunsIn (program arithmetic)
      (K + 20 * (left.length + right.length) + 8 * out.length + 69)
      ((⟨regs, s⟩ : Data).withPC (some (program arithmetic).entry))
      ((⟨fun _ => false,
        Function.update s 27 (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none) := by
  have hprepare := prepare_run s left right tail hin h21 h29 h120 h240 h241
  have hfinish := finish_run s left right tail out h29 h240 h241 h244
  obtain ⟨na, ra, hna, hea⟩ := hprepare regs
  obtain ⟨nb, rb, hnb, heb⟩ := harithmetic ra
  obtain ⟨nc, rc, hnc, hec⟩ := hfinish rb
  have hed := reset_eval rc (Function.update s 27 (true :: (Encoding.frame out ++ tail)))
  refine ⟨na + (nb + (nc + 17)) + 1, by omega, ?_⟩
  exact compiled_halt_trace (hea.seq (heb.seq (hec.seq hed))) 27 27

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn_oai
