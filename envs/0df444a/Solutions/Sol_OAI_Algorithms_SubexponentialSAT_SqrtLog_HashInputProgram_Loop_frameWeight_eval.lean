-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:23:42.511987+00:00
-- url     : https://prove2.me/submissions/5392dcce-671d-4dcd-8720-8ea0687fc3ec

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem frameBody_eval (regs : Fin 3 → Bool) (b : Bool)
    (source output : List Bool) (htrue : regs 2 = true) :
    Eval frameBody 3 (frameReady regs (b :: source) output)
      (frameReady (readRegs regs 0 1 (some b)) source (true :: b :: output)) := by
  let d := frameReady regs (b :: source) output
  let d1 := (Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have hh := Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (0 : Fin 3)) d)
    (Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) d1)
      (Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) d2))
  convert hh using 1 ;
    simp [ frameReady, frameData, d, d1, d2, Atom.eval, Atom.instr,
      State.ofCfg, execInstr, readRegs, htrue] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem frameLoop_eval (source output : List Bool) (regs : Fin 3 → Bool)
    (htrue : regs 2 = true) :
    ∃ final, final 2 = true ∧ Eval frameLoop (4 * source.length + 1)
      (frameReady regs source output) (frameData final [] (emitPairs source output)) := by
  induction source generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 none, by simpa [readRegs] using htrue, ?_⟩
    apply Eval.while_false
    simp [frameReady, frameData, readRegs]
  | cons b bs ih =>
    have hr : (readRegs regs 0 1 (some b)) 2 = true := by simpa [readRegs] using htrue
    obtain ⟨final, hf, he⟩ := ih (true :: b :: output) (readRegs regs 0 1 (some b)) hr
    refine ⟨final, hf, ?_⟩
    have hh := Eval.while_true
      (by simp [frameReady, frameData, readRegs] : (frameReady regs (b :: bs) output).regs 1 = true)
      (frameBody_eval regs b bs output htrue) he
    have hc : 3 + (4 * bs.length + 1) + 1 = 4 * (b :: bs).length + 1 := by simp; omega
    rw [hc] at hh
    exact hh

theorem emitPairs_append (a b out : List Bool) :
    emitPairs (a ++ b) out = emitPairs b (emitPairs a out) := by
  induction a generalizing out with
  | nil => rfl
  | cons x xs ih => simpa [emitPairs] using ih (true :: x :: out)

theorem emitPairs_frame (source out : List Bool) :
    emitPairs source.reverse (false :: out) = Encoding.frame source ++ out := by
  induction source with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, emitPairs_append, emitPairs, ih, Encoding.frame ]

theorem frameEmit_eval (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Eval frameEmit (4 * source.length + 5)
      (frameData regs source.reverse output)
      (frameData final [] (Encoding.frame source ++ output)) := by
  let r0 := Function.update regs (2 : Fin 3) false
  let r1 := Function.update r0 (2 : Fin 3) true
  have h0 : Eval (.atom (.set 2 false)) 1 (frameData regs source.reverse output)
      (frameData r0 source.reverse output) := Eval.atom _ _
  have h1 : Eval (.atom (.push 1 2)) 1 (frameData r0 source.reverse output)
      (frameData r0 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) (frameData r0 source.reverse output) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, r0]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h2 : Eval (.atom (.set 2 true)) 1 (frameData r0 source.reverse (false :: output))
      (frameData r1 source.reverse (false :: output)) := Eval.atom _ _
  have h3 : Eval (.atom (.pop 0 0 1)) 1 (frameData r1 source.reverse (false :: output))
      (frameReady r1 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) (frameData r1 source.reverse (false :: output)) using 1
    all_goals try with_reducible_and_instances rfl
    cases source.reverse <;>
      simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, frameReady] ;
      (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨final, _, hf⟩ := frameLoop_eval source.reverse (false :: output) r1 (by simp [r1])
  rw [emitPairs_frame] at hf
  refine ⟨final, ?_⟩
  have hh := h0.seq (h1.seq (h2.seq (h3.seq hf)))
  convert hh using 1 ; simp [] ; omega

theorem frameEmit_trace (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Trace frameEmitProgram (4 * source.length + 6)
      ((frameData regs source.reverse output).withPC (some frameEmitProgram.entry))
      ((frameData final [] (Encoding.frame source ++ output)).withPC none) := by
  obtain ⟨final,hf⟩ := frameEmit_eval source output regs
  refine ⟨final, ?_⟩
  simpa [frameEmitProgram, Nat.add_assoc] using compiled_halt_trace hf 0 1
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem emitPorts_injective : Function.Injective emitPorts := by decide

theorem reverseWeight_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    Eval reverseWeight (3*weight.length+3) (data regs weight clause [])
      (data (readRegs regs 0 1 none) [] clause weight.reverse) := by
  have h := transfer_eval (data regs weight clause []) 0 2 0 1 (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem emit_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, Eval emit (4*weight.length+6)
      (data regs [] clause weight.reverse)
      (data rr [] (Encoding.frame weight ++ clause) []) := by
  obtain ⟨rr,ht⟩ := Squarefree.Program.frameEmit_trace weight clause regs
  have hi : embedState id emitPorts (data regs [] clause weight.reverse)
      (Squarefree.Program.frameData regs weight.reverse clause) =
      data regs [] clause weight.reverse := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have ho : embedState id emitPorts (data regs [] clause weight.reverse)
      (Squarefree.Program.frameData rr [] (Encoding.frame weight ++ clause)) =
      data rr [] (Encoding.frame weight ++ clause) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [data,emitPorts,Fin.exists_fin_succ]
  have he := eval_call_lifted Squarefree.Program.frameEmitProgram id emitPorts
    (data regs [] clause weight.reverse) Function.injective_id emitPorts_injective ht
  rw [hi,ho] at he
  exact ⟨rr,he⟩

theorem command_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, Eval command (7*weight.length+9)
      (data regs weight clause [])
      (data rr [] (Encoding.frame weight ++ clause) []) := by
  obtain ⟨rr,he⟩ := emit_eval (readRegs regs 0 1 none) weight clause
  refine ⟨rr,?_⟩
  have hh := (reverseWeight_eval regs weight clause).seq he
  convert hh using 1 <;> first | rfl | omega

theorem program_runs (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, RunsIn program (7*weight.length+10)
      ((data regs weight clause []).withPC (some program.entry))
      ((data rr [] (Encoding.frame weight ++ clause) []).withPC none) := by
  obtain ⟨rr,he⟩ := command_eval regs weight clause
  exact ⟨rr,⟨7*weight.length+9+1,by omega,compiled_halt_trace he 0 1⟩⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assembly of one raw tuple term. All source lookup, coefficient lifting,
and record framing are executed by fixed native programs. The only persistent
data are the unexpanded original source, word width, modulus, ring shape,
unread raw bytes, and the already emitted output. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem embed_tapes {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 24)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 24 → List Bool)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs,target⟩ : Data) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j,rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by decide

theorem frameWeight_eval_oai (regs : Fin 8 → Bool)
    (rest width modulus master shape acc weight payload : List Bool) :
    ∃ n ≤ 7*weight.length+10, ∃ rf,
      Eval frameWeight n (data regs rest width modulus master shape acc weight [] payload [])
        (data rf rest width modulus master shape acc [] [] (Encoding.frame weight++payload) []) := by
  let a := data regs rest width modulus master shape acc weight [] payload []
  obtain ⟨rf,n,hn,hr⟩ := Frame.program_runs (regs ∘ lowRegisters) weight payload
  have hi : projectState lowRegisters frameStacks a =
      Frame.data (regs ∘ lowRegisters) weight payload [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← hi] at hr
  have he := eval_call_from_state Frame.program lowRegisters frameStacks a
    lowRegisters_injective frameStacks_injective hr
  have ho := embed_tapes lowRegisters frameStacks frameStacks_injective a
    (Frame.data rf [] (Encoding.frame weight++payload) [])
    (tapes rest width modulus master shape acc [] [] (Encoding.frame weight++payload) [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h6 : i ≠ 6 := fun hh => h ⟨0,hh.symm⟩
      have h18 : i ≠ 18 := fun hh => h ⟨1,hh.symm⟩
      fin_cases i <;> simp_all [a,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval_oai
