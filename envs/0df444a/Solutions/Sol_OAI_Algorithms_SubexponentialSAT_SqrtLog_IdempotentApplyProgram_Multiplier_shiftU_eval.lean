-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:47:22.62328+00:00
-- url     : https://prove2.me/submissions/bac32975-dde2-4d34-9d89-58c26410922d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_KeyMapProgram_clip_store
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_KeyMapProgram_join_store

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frameReadRegs_injective : Function.Injective frameReadRegs := Fin.castAdd_injective _ _
theorem frameReadPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (frameReadPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [frameReadPorts, ParserProgram.pair]

theorem readFrame8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst)
    (bits : List Bool) (rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame8 src dst) (6 * bits.length + 4) d (afterFrame8 d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState frameReadRegs (frameReadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState frameReadRegs (frameReadPorts src dst) d b = afterFrame8 d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [frameReadRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [frameReadRegs] using h.symm⟩
      simp [afterFrame8, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [frameReadPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [frameReadPorts] using h.symm⟩
      simp [afterFrame8, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram frameReadRegs
    (frameReadPorts src dst) d frameReadRegs_injective (frameReadPorts_injective src dst hsd) ht
  simpa only [ha,hb,readFrame8] using h

theorem transfer8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst) :
    Eval (transfer8 src dst) (3*(d.stacks src).length+3) d (afterTransfer8 d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [afterTransfer8,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem rawEntries_append (a b : List ByteRecord) :
    rawEntries (a++b) = rawEntries a ++ rawEntries b := by
  induction a with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨k,c⟩; simp [rawEntries,ih,List.append_assoc]

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (hst : src ≠ 7) (htd : (7 : Fin 15) ≠ dst)
    (htmp : a.tmp = []) (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.copy_run src dst 7 0 1 hsd hst htd
    (by decide) regs (tapes a) (by simpa [tapes] using htmp)
  apply Eval.call
  simpa only [state, ListRegisterProgram.Run, StructuredProgram.State.withPC, hout] using he

theorem read_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hout : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state, Program.afterFrame8, hout] using
    Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

theorem transfer_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (Program.transfer8 src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [state, Program.afterTransfer8, hout] using
    Program.transfer8_eval (state regs a) src dst hsd

theorem clear_store (regs : Fin 8 → Bool) (a b : Store) (src : Fin 15)
    (hout : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.clear_run src (0 : Fin 8) 1 regs (tapes a)
  apply Eval.call
  simpa only [state, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    clearStacks, hout] using he

theorem peek_eval (regs : Fin 8 → Bool) (s : Store) :
    Eval peek 1 (state regs s) (state (readRegs regs 0 1 s.source.head?) s) :=
  .base (.atom _ _)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem regs3_inj : Function.Injective regs3 := Fin.castAdd_injective _ _
theorem emitPorts_inj : Function.Injective emitPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [emitPorts]

theorem emit_store (regs : Fin 8 → Bool) (s : Store) (key coeff : List Bool)
    (hk : s.joinedRev = key.reverse) (hc : s.coeffRev = coeff.reverse) :
    ∃ rr, Eval emit (4*key.length+4*coeff.length+13) (state regs s)
      (state rr {s with joinedRev := [], coeffRev := [], output := Encoding.frame key ++ Encoding.frame coeff ++ s.output}) := by
  obtain ⟨rf,ht⟩ := Program.prependRecord_trace (regs ∘ regs3) key coeff s.output
  let finish := Program.prependData rf [] [] (Encoding.frame key ++ Encoding.frame coeff ++ s.output)
  let rr := (embedState regs3 emitPorts (state regs s) finish).regs
  have hs : embedState regs3 emitPorts (state regs s)
      (Program.prependData (regs ∘ regs3) key.reverse coeff.reverse s.output) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs3_inj emitPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [Program.prependData,emitPorts,state,tapes,hk,hc]
    · intros; rfl
  have hf : embedState regs3 emitPorts (state regs s) finish =
      state rr {s with joinedRev := [], coeffRev := [], output := Encoding.frame key ++ Encoding.frame coeff ++ s.output} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs3_inj emitPorts_inj
    · intro i; exact embedState_register regs3 emitPorts (state regs s) finish regs3_inj i
    · intro i hi; exact embedState_register_frame regs3 emitPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,Program.prependData,emitPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [emitPorts,state,tapes,Fin.exists_fin_succ]
  have he := eval_call_lifted Program.prependRecordProgram regs3 emitPorts
    (state regs s) regs3_inj emitPorts_inj ht
  dsimp only [finish] at hf
  exact ⟨rr,by simpa only [emit,hs,hf] using he⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem prepare_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) :
    ∃ rr, Eval prepare (9*key.length+6*coeff.length+7*e.leftKey.length+16)
      (state regs (idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) output))
      (state rr (prepared e key coeff tail output)) := by
  let a := idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) output
  let b := {a with source := Encoding.frame coeff ++ tail, keyRev := key.reverse}
  let c := {b with source := tail, coeffRev := coeff.reverse}
  let d := {c with keyRev := [], rightKey := key}
  let f := prepared e key coeff tail output
  let r1 := readRegs regs 0 1 (some false)
  let r2 := readRegs r1 0 1 (some false)
  let r3 := readRegs r2 0 1 none
  have h1 := read_store regs a b 0 5 (by decide) key (Encoding.frame coeff ++ tail)
    (by simp [a,idle,tapes,List.append_assoc])
    (by funext i; fin_cases i <;> simp [a,b,idle,tapes])
  have h2 := read_store r1 b c 0 6 (by decide) coeff tail rfl
    (by funext i; fin_cases i <;> simp [a,b,c,idle,tapes])
  have h3 := transfer_store r2 c d 5 8 (by decide)
    (by funext i; fin_cases i <;> simp [a,b,c,d,idle,tapes,transferStacks])
  have h4 := copy_store r3 d f 1 9 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,f,prepared,idle,tapes,copyStacks])
  have he := h1.seq (h2.seq (h3.seq h4))
  refine ⟨readRegs r3 0 1 none,?_⟩
  convert he using 1 ;
    simp [a,b,c,d,idle,tapes] ; omega

theorem prepareClip_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) :
    ∃ rr, Eval prepareClip
      (10*key.length+7*e.tMaster.length+7*e.jMaster.length+18)
      (state regs (joined e key coeff tail output))
      (state rr (clipReady e key coeff tail output)) := by
  let a := joined e key coeff tail output
  let b := {a with keyRev := key.reverse}
  let c := {b with keyRev := [], clipKey := key}
  let d := {c with tCopy := e.tMaster}
  let f := clipReady e key coeff tail output
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := copy_store regs a b 10 5 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes,copyStacks])
  have h2 := transfer_store r1 b c 5 11 (by decide)
    (by funext i; fin_cases i <;> simp [a,b,c,joined,idle,tapes,transferStacks])
  have h3 := copy_store r2 c d 2 12 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,joined,idle,tapes,copyStacks])
  have h4 := copy_store r3 d f 3 13 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,f,clipReady,joined,idle,tapes,copyStacks])
  have he := h1.seq (h2.seq (h3.seq h4))
  refine ⟨readRegs r3 0 1 none,?_⟩
  convert he using 1 ;
    simp [a,b,c,d,joined,idle,tapes] ; omega

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finish_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) (flag : Bool) (hf : regs 4 = flag) :
    ∃ time ≤ 4*key.length+4*coeff.length+14, ∃ rr,
      Eval finish time (state regs (joined e key coeff tail output))
        (state rr (idle e tail
          (if flag then Encoding.frame key ++ Encoding.frame coeff ++ output else output))) := by
  cases flag with
  | true =>
    obtain ⟨rr,he⟩ := emit_store regs (joined e key coeff tail output) key coeff rfl rfl
    refine ⟨(4*key.length+4*coeff.length+13)+1,by omega,rr,?_⟩
    have ht := Eval.ite_true (no := .seq (clear 10) (clear 6)) (by simpa [state] using hf) he
    simpa [finish,joined,idle] using ht
  | false =>
    let a := joined e key coeff tail output
    let b := {a with joinedRev := []}
    have h1 := clear_store regs a b 10
      (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes])
    have h2 := clear_store (readRegs regs 0 1 none) b (idle e tail output) 6
      (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes])
    refine ⟨(2*key.length+3)+(2*coeff.length+3)+1,?_,
      readRegs (readRegs regs 0 1 none) 0 1 none,?_⟩
    · simp []
      omega
    · have ht := Eval.ite_false (yes := emit) (by simpa [state] using hf) (h1.seq h2)
      simpa [finish,a,b,joined,idle,tapes] using ht

theorem step_eval {n : ℕ} (regs : Fin 8 → Bool) (a b : Index (Fin n)) (t J : ℕ)
    (coeff tail output : List Bool) :
    ∃ time ≤ stepBudget a b t J coeff.length, ∃ rr,
      Eval step time
        (state regs (idle (environment a t J)
          (Encoding.frame (encodeIndex b) ++ Encoding.frame coeff ++ tail) output))
        (state rr (idle (environment a t J) tail
          (if (a.join b).Kept t J then
            Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame coeff ++ output
          else output))) := by
  let e := environment a t J
  obtain ⟨r1,h1⟩ := prepare_eval regs e (encodeIndex b) coeff tail output
  obtain ⟨r2,h2⟩ := join_store r1 (prepared e (encodeIndex b) coeff tail output) a b rfl rfl rfl
  have h2' : Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22)
      (state r1 (prepared e (encodeIndex b) coeff tail output))
      (state r2 (joined e (encodeIndex (a.join b)) coeff tail output)) := by
    simpa [prepared,joined,idle] using h2
  obtain ⟨r3,h3⟩ := prepareClip_eval r2 e (encodeIndex (a.join b)) coeff tail output
  obtain ⟨c,hc,r4,h4,hflag⟩ := clip_store r3
    (clipReady e (encodeIndex (a.join b)) coeff tail output) (a.join b) t J rfl rfl rfl rfl
  have h4' : Eval clip c
      (state r3 (clipReady e (encodeIndex (a.join b)) coeff tail output))
      (state r4 (joined e (encodeIndex (a.join b)) coeff tail output)) := by
    simpa [clipReady,joined,idle] using h4
  obtain ⟨f,hf,r5,h5⟩ := finish_eval r4 e (encodeIndex (a.join b)) coeff tail output
    (decide ((a.join b).Kept t J)) hflag
  refine ⟨_,?_,r5,by simpa [step] using h1.seq (h2'.seq (h3.seq (h4'.seq h5)))⟩
  simp only [stepBudget,e,environment,List.length_replicate,encodeIndex_length,Index.join] at hc hf ⊢
  omega

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem ready_nil_guard {n : ℕ} (regs : Fin 8 → Bool) (a : Index (Fin n))
    (t J : ℕ) (output : List Bool) : (ready regs a t J [] output).regs 1 = false := by
  simp [ready,encoded,Program.rawEntries,state,readRegs]

theorem ready_cons_guard {n : ℕ} (regs : Fin 8 → Bool) (a b : Index (Fin n))
    (t J : ℕ) (c : List Bool) (rest : List (Entry n)) (output : List Bool) :
    (ready regs a t J ((b,c)::rest) output).regs 1 = true := by
  cases h : encodeIndex b <;>
    simp [ready,encoded,Program.rawEntries,state,readRegs,Encoding.frame,h]

theorem loop_eval {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries, ∃ rr,
      Eval loop time (ready regs a t J entries output)
        (state rr (idle (environment a t J) [] (accumulated a t J entries output))) := by
  induction entries generalizing output regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 1 none,?_⟩
    exact Eval.while_false (ready_nil_guard regs a t J output)
  | cons entry entries ih =>
    rcases entry with ⟨b,c⟩
    let rg := readRegs regs 0 1 (Program.rawEntries (encoded ((b,c)::entries))).head?
    let out := if (a.join b).Kept t J then
      Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame c ++ output else output
    obtain ⟨s,hs,middle,he⟩ := step_eval rg a b t J c (Program.rawEntries (encoded entries)) output
    obtain ⟨v,hv,rr,ht⟩ := ih out middle
    have hp := peek_eval middle (idle (environment a t J) (Program.rawEntries (encoded entries)) out)
    refine ⟨s+1+v+1,?_,rr,?_⟩
    · simp only [budget]
      omega
    · have hh := Eval.while_true (ready_cons_guard regs a b t J c entries output) (he.seq hp) ht
      exact hh

theorem accumulated_eq {n : ℕ} (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) (output : List Bool) :
    accumulated a t J entries output =
      Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output := by
  induction entries generalizing output with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨b,c⟩
    by_cases hk : (a.join b).Kept t J <;>
      simp [accumulated,mapped,hk,ih,encoded,List.reverse_cons,Program.rawEntries_append,
        Program.rawEntries,List.append_assoc]

theorem scan_eval {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries + 1, ∃ rr,
      Eval scan time
        (state regs (idle (environment a t J) (Program.rawEntries (encoded entries)) output))
        (state rr (idle (environment a t J) []
          (Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output))) := by
  obtain ⟨time,ht,rr,he⟩ := loop_eval a t J entries output regs
  rw [accumulated_eq] at he
  refine ⟨1+time,by omega,rr,?_⟩
  exact (peek_eval regs _).seq he

theorem scan_trace {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries + 2, ∃ rr,
      Trace scanProgram time
        ((state regs (idle (environment a t J) (Program.rawEntries (encoded entries)) output)).withPC
          (some scanProgram.entry))
        ((state rr (idle (environment a t J) []
          (Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output))).withPC none) := by
  obtain ⟨time,ht,rr,he⟩ := scan_eval a t J entries output regs
  exact ⟨time+1,by omega,rr,compiled_halt_trace he 0 4⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


theorem mapPorts_injective : Function.Injective mapPorts := by decide

/-- The key-map call preserves its key and capacity tapes and all surrounding memory. -/
theorem shiftU_command_eval {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
    (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (hk:x.stacks 94=Squarefree.encodeIndex a)
    (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
    (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
      Eval shiftUCommand k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
        (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩ := by
  have h80:=hclean 80 (by simp)
  have h81:=hclean 81 (by simp)
  have h82:=hclean 82 (by simp)
  have h83:=hclean 83 (by simp)
  have h84:=hclean 84 (by simp)
  have h85:=hclean 85 (by simp)
  have h89:=hclean 89 (by simp)
  have h90:=hclean 90 (by simp)
  have h91:=hclean 91 (by simp)
  have h92:=hclean 92 (by simp)
  let initial:=Squarefree.KeyMapProgram.state x.regs (Squarefree.KeyMapProgram.idle (Squarefree.KeyMapProgram.environment a u J)
    (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries)) (x.stacks 86))
  have hi : projectState id mapPorts x=initial := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [mapPorts,Squarefree.KeyMapProgram.tapes,Squarefree.KeyMapProgram.idle,Squarefree.KeyMapProgram.environment,hs,hk,hu,hJ,
          h80,h81,h82,h83,h84,h85,h89,h90,h91,h92]
  obtain ⟨k,hbound,rr,ht⟩:=Squarefree.KeyMapProgram.scan_trace a u J entries (x.stacks 86) x.regs
  dsimp only [initial] at hi
  rw [←hi] at ht
  have he:=eval_call_from_state Squarefree.KeyMapProgram.scanProgram id mapPorts x
    Function.injective_id mapPorts_injective ht
  refine ⟨k,hbound,rr,?_⟩
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  symm
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id mapPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;>
      simp [mapPorts,Squarefree.KeyMapProgram.state,Squarefree.KeyMapProgram.tapes,Squarefree.KeyMapProgram.idle,Squarefree.KeyMapProgram.environment,hk,hu,hJ,
        h80,h81,h82,h83,h84,h85,h89,h90,h91,h92]
  · intro i hi
    have h67:i≠67:=by intro he; apply hi; exact ⟨0,he.symm⟩
    have h86:i≠86:=by intro he; apply hi; exact ⟨4,he.symm⟩
    simp [h67,h86]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem shiftU_eval_oai {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
    (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (hk:x.stacks 94=Squarefree.encodeIndex a)
    (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
    (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
      Eval shiftU k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
        (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩ := by
  simpa only [shiftU,shiftUCommand,shiftPorts,mapPorts] using
    shiftU_command_eval a u J entries x hs hk hu hJ hclean

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval_oai
