-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:14:59.946113+00:00
-- url     : https://prove2.me/submissions/0f67ee7f-7bb8-48e1-a44d-d19e1e7044ec

import Mathlib
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

private theorem transfer_output (word : List Bool) :
    SubexponentialSAT.StackRoutines.transferStacks (2 : Fin 3) 0 (operandStacks [] [] word) =
      operandStacks word.reverse [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.transferStacks, operandStacks]

/-- Sequentially link a proved arithmetic run to a proved transfer run.
Both runs execute inside the concrete linked finite instruction table. -/
theorem append_reverse_output {l : ℕ} (p : Program 8 3 l)
    {n : ℕ} {start : Cfg 8 3 l} (regs : Fin 8 → Bool) (word : List Bool)
    (hrun : Trace p n start ⟨none, regs, operandStacks [] [] word⟩) :
    Trace (SubexponentialSAT.ProgramLinking.link p reverseOutput)
      (n + 3 * word.length + 3)
      (SubexponentialSAT.ProgramLinking.relabelCfg (Fin.castAdd 4)
        (some (Fin.natAdd l reverseOutput.entry)) start)
      ⟨none, readRegs regs 1 3 none, operandStacks word.reverse [] []⟩ := by
  have ht := SubexponentialSAT.StackRoutines.transferProgram_trace
    (2 : Fin 3) 0 (1 : Fin 8) 3 (by decide) (by decide)
    regs (operandStacks [] [] word)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace reverseOutput ht
    (3 : Fin 4) rfl rfl
  have hlink := SubexponentialSAT.ProgramLinking.link_trace p reverseOutput hrun rfl hh
  simpa [SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc,
    SubexponentialSAT.StackRoutines.transferResult, transfer_output, Nat.add_assoc] using hlink

theorem paddingLE_correct (regs : Fin 8 → Bool) (shape input : List Bool)
    (hlen : input.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingLEProgram (7 * shape.length + 6)
        ⟨some 0, regs, operandStacks shape input []⟩
        ⟨none, finalRegs, operandStacks (padTo shape input) [] []⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨midRegs, hrun, hborrow⟩ := padding_correct regs shape input [] hlen
  have hrun' : Trace paddingProgram (4 * shape.length + 3)
      (paddingCfg (some 0) regs shape input [])
      ⟨none, midRegs, operandStacks [] [] (padTo shape input).reverse⟩ := by
    simpa [paddingCfg] using hrun
  have hout := append_reverse_output paddingProgram midRegs _ hrun'
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · convert hout using 1
    · rw [List.length_reverse, padTo_length]
      omega
    · rfl
    · rw [List.reverse_reverse]
  · simpa [readRegs] using hborrow

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators


namespace PadScore

open ModularPrograms ModularArithmetic

private theorem pads_injective : Function.Injective pads := by decide

theorem command_eval (regs : Fin 8 → Bool) (score shape : List Bool)
    (hlen : score.length ≤ shape.length) :
    ∃ rf, Eval command (23 * shape.length + 19) (data regs score shape)
      (data rf (padTo shape score) shape) := by
  let a := data regs score shape
  let r1 := readRegs regs 0 1 none
  let a1 : State 8 5 := ⟨r1, ![score,shape,shape,[],[]]⟩
  have h1 := Subexp.TupleProgram.copy_eval (1 : Fin 5) 2 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a rfl
  have he1 : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 1 2 a.stacks⟩ :
      State 8 5) = a1 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext i
    fin_cases i <;> simp [a, data, StackRoutines.copyStacks]
  rw [he1] at h1
  obtain ⟨r2, h2, _⟩ := paddingLE_correct r1 shape score hlen
  let d2 : State 8 3 := ⟨r2, operandStacks (padTo shape score) [] []⟩
  have h2' : Trace paddingLEProgram (7 * shape.length + 6)
      ((projectState id pads a1).withPC (some paddingLEProgram.entry)) (d2.withPC none) := by
    have hproject : projectState id pads a1 = ⟨r1, operandStacks shape score []⟩ := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    rw [hproject]
    have hentry : paddingLEProgram.entry = (0 : Fin 9) := by
      apply Fin.ext
      rfl
    rw [hentry]
    exact h2
  have he2 := eval_call_from_state paddingLEProgram id pads a1
    Function.injective_id pads_injective h2'
  let a2 : State 8 5 := ⟨r2, ![[],shape,padTo shape score,[],[]]⟩
  have ha2 : embedState id pads a1 d2 = a2 := by
    apply embedState_eq_of_ports id pads a1 a2 d2 Function.injective_id pads_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi ⟨1, rfl⟩)
      · rfl
      · exact False.elim (hi ⟨0, rfl⟩)
      · rfl
      · rfl
  rw [ha2] at he2
  have h3 := Subexp.TupleProgram.copy_eval (2 : Fin 5) 0 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a2 rfl
  let a3 : State 8 5 := ⟨readRegs r2 0 1 none,
    ![padTo shape score,shape,padTo shape score,[],[]]⟩
  have ha3 : (⟨readRegs a2.regs 0 1 none, StackRoutines.copyStacks 2 0 a2.stacks⟩ :
      State 8 5) = a3 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext i
    fin_cases i <;> simp [a2, StackRoutines.copyStacks]
  rw [ha3] at h3
  have h4 := Subexp.TupleProgram.clear_eval (2 : Fin 5) (0 : Fin 8) 1 a3
  have ha4 : (⟨readRegs a3.regs 0 1 none, StackRoutines.clearStacks 2 a3.stacks⟩ :
      State 8 5) = data (readRegs r2 0 1 none) (padTo shape score) shape := by
    apply congrArg₂ StructuredProgram.State.mk
    · exact StackRoutines.readRegs_reset r2 0 1 none
    funext i
    fin_cases i <;> simp [a3, StackRoutines.clearStacks]
  rw [ha4] at h4
  refine ⟨readRegs r2 0 1 none, ?_⟩
  convert h1.seq (he2.seq (h3.seq h4)) using 1
  · rfl
  · simp [a, a2, a3, data, padTo_length]
    omega

theorem trace_space (regs : Fin 8 → Bool) (score shape : List Bool)
    (hlen : score.length ≤ shape.length) :
    ∃ rf, Trace program (23 * shape.length + 20)
      ((data regs score shape).withPC (some program.entry))
      ((data rf (padTo shape score) shape).withPC none) ∧
      ∀ k c, k ≤ 23 * shape.length + 20 →
        Trace program k ((data regs score shape).withPC (some program.entry)) c →
        ∀ i, (c.stacks i).length ≤ 25 * shape.length + 20 := by
  obtain ⟨rf, he⟩ := command_eval regs score shape hlen
  refine ⟨rf, compiled_halt_trace he 0 0, ?_⟩
  have hb : dataBits ((data regs score shape).withPC (some program.entry)) ≤
      2 * shape.length := by
    simp [dataBits, stackBits, data, Fin.sum_univ_succ]
    omega
  intro k c hk hc i
  have h := StructuredSpace.local_stack_bound program (steps := 23 * shape.length + 20)
    hb k c hk hc i
  omega

theorem leaf_eval_oai (a : State 40 896) (h0 : a.stacks 0 = [])
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hlen : (a.stacks 769).length ≤ (a.stacks 818).length) :
    ∃ b, Eval leafCommand (23 * (a.stacks 818).length + 20) a b ∧
      b.stacks = Function.update a.stacks 769
        (padTo (a.stacks 818) (a.stacks 769)) := by
  let d := projectState leafRegisters leafStacks a
  have hd : d = data d.regs (a.stacks 769) (a.stacks 818) := by
    apply CounterForPrograms.data_ext (a := d)
      (b := data d.regs (a.stacks 769) (a.stacks 818)) rfl
    funext i
    fin_cases i <;> simp [d, data, projectState, leafStacks, h0, h1, h2]
  obtain ⟨rf, ht, _⟩ := trace_space d.regs (a.stacks 769) (a.stacks 818) hlen
  rw [← hd] at ht
  have hr : Function.Injective leafRegisters := Fin.castAdd_injective 8 32
  have hs : Function.Injective leafStacks := by decide
  let out := data rf (padTo (a.stacks 818) (a.stacks 769)) (a.stacks 818)
  refine ⟨embedState leafRegisters leafStacks a out,
    eval_call_from_state program leafRegisters leafStacks a hr hs ht, ?_⟩
  have hout : out.stacks = Function.update d.stacks 0
      (padTo (a.stacks 818) (a.stacks 769)) := by
    funext i
    fin_cases i <;> simp [out, data, d, projectState, leafStacks, h0, h1, h2]
  change Function.extend leafStacks out.stacks a.stacks = _
  rw [hout, ProgramLinking.extend_update hs]
  have hf : Function.extend leafStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project leafRegisters leafStacks a hr hs)
  rw [hf]
  rfl

end PadScore

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval_oai
