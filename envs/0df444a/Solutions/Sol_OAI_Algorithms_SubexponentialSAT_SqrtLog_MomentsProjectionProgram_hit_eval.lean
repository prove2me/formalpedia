-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:58:50.301615+00:00
-- url     : https://prove2.me/submissions/3364dde6-1786-45bf-9821-22d0654c1b80

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S109

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem payloadPorts_injective : Function.Injective payloadPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [payloadPorts]
theorem keyPorts_injective : Function.Injective keyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [keyPorts]

theorem embedPayload (regs rr : Fin 3 → Bool) (key coeff output coeff' output' : List Bool) :
    embedState id payloadPorts (prependData regs key coeff output) (frameData rr coeff' output') =
      prependData rr key coeff' output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id payloadPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [payloadPorts,prependData,Fin.exists_fin_succ]

theorem embedKey (regs rr : Fin 3 → Bool) (key coeff output key' output' : List Bool) :
    embedState id keyPorts (prependData regs key coeff output) (frameData rr key' output') =
      prependData rr key' coeff output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [keyPorts,prependData,Fin.exists_fin_succ]

theorem prependRecord_eval (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Eval prependRecord (4 * key.length + 4 * coeff.length + 12)
      (prependData regs key.reverse coeff.reverse output)
      (prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)) := by
  obtain ⟨r1,hp⟩ := frameEmit_trace coeff output regs
  have hp' := eval_call_lifted frameEmitProgram id payloadPorts
    (prependData regs key.reverse coeff.reverse output)
    Function.injective_id payloadPorts_injective hp
  simp only [embedPayload] at hp'
  obtain ⟨r2,hk⟩ := frameEmit_trace key (Encoding.frame coeff ++ output) r1
  have hk' := eval_call_lifted frameEmitProgram id keyPorts
    (prependData r1 key.reverse [] (Encoding.frame coeff ++ output))
    Function.injective_id keyPorts_injective hk
  simp only [embedKey] at hk'
  refine ⟨r2,?_⟩
  convert hp'.seq hk' using 1 <;> try omega
  simp [List.append_assoc]

theorem prependRecord_trace (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Trace prependRecordProgram (4 * key.length + 4 * coeff.length + 13)
      ((prependData regs key.reverse coeff.reverse output).withPC (some prependRecordProgram.entry))
      ((prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)).withPC none) := by
  obtain ⟨final,he⟩ := prependRecord_eval regs key coeff output
  exact ⟨final,by simpa [prependRecordProgram,Nat.add_assoc] using compiled_halt_trace he 0 2⟩
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem transfer_machine (regs : Fin 5 → Bool) (a b : Tape) (src dst : Fin 10)
    (hsd : src ≠ dst) (hs : StackRoutines.transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0:Fin 5) 1 hsd (by decide) regs (tapes a)
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transfer,machine,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc,hs] using hh

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem emitPorts_injective : Function.Injective emitPorts := by decide

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Emit one framed record without touching the outer source or accumulated output. -/
theorem emit_eval (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
    (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) :
    ∃ rf, Eval emit (4*key.length+4*coeff.length+13) (machine regs a)
      (machine rf {a with newkey:=[],coeff:=[], framed:=Encoding.frame key++Encoding.frame coeff++a.framed}) := by
  obtain ⟨rr,hh⟩ := Squarefree.Program.prependRecord_trace (regs ∘ smallRegs) key coeff a.framed
  let b := Squarefree.Program.prependData rr [] []
    (Encoding.frame key++Encoding.frame coeff++a.framed)
  let rf := (embedState smallRegs emitPorts (machine regs a) b).regs
  have ha : embedState smallRegs emitPorts (machine regs a)
      (Squarefree.Program.prependData (regs ∘ smallRegs) key.reverse coeff.reverse a.framed) =
        machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective emitPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [machine,tapes,Squarefree.Program.prependData,emitPorts,hk,hc]
    · intros; rfl
  have hb : embedState smallRegs emitPorts (machine regs a) b =
      machine rf {a with newkey:=[],coeff:=[], framed:=Encoding.frame key++Encoding.frame coeff++a.framed} := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective emitPorts_injective
    · intro i; exact embedState_register smallRegs emitPorts (machine regs a) b smallRegs_injective i
    · intro i hi; exact embedState_register_frame smallRegs emitPorts (machine regs a) b i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [emitPorts,machine,tapes,Fin.exists_fin_succ]
  have h := eval_call_lifted Squarefree.Program.prependRecordProgram smallRegs emitPorts
    (machine regs a) smallRegs_injective emitPorts_injective hh
  exact ⟨rf,by simpa only [ha,hb,emit,b] using h⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A successful record is prepended to the reversed accumulator. -/
theorem hit_eval_oai (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
    (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) (hf : a.framed = []) :
    ∃ rf, Eval hit (4*key.length+4*coeff.length+13+
        (3*(Encoding.frame key++Encoding.frame coeff).length+3))
      (machine regs a)
      (machine rf {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output}) := by
  obtain ⟨r₁,h₁⟩ := emit_eval regs a key coeff hk hc
  let b : Tape := {a with newkey:=[],coeff:=[],framed:=Encoding.frame key++Encoding.frame coeff}
  let c : Tape := {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output}
  have h₁' : Eval emit (4*key.length+4*coeff.length+13) (machine regs a) (machine r₁ b) := by
    simpa [b,hf] using h₁
  have h₂ := transfer_machine r₁ b c 9 8 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,b,c])
  refine ⟨readRegs r₁ 0 1 none,?_⟩
  simpa [hit,b,tapes,c] using h₁'.seq h₂

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval_oai
