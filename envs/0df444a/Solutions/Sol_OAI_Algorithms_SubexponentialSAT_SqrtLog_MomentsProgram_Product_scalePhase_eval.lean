-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:20:56.621699+00:00
-- url     : https://prove2.me/submissions/99bfef46-cc65-4bf7-9341-50eed04588bf

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S135
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S153

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem nativePorts_injective : Function.Injective nativePorts :=
  Fin.castAdd_injective _ _

theorem embed_native (regs rr : Fin 8 → Bool) (s : Store) (native : RingScan.ServiceStore) :
    embedState id nativePorts (state regs s) (RingScan.serviceWorkState rr native) =
      state rr {s with native := native} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;>
      simp [state, tapes, nativePorts, RingScan.serviceWorkState, RingScan.serviceTapes]
  · intro i hi
    apply Fin.addCases (m := 32) (n := 8) (motive := fun i =>
      i ∉ Set.range nativePorts → (state rr {s with native := native}).stacks i =
        (state regs s).stacks i) ?_ ?_ i hi
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; fin_cases j <;> simp [state, tapes]

theorem copy_eval (d : Data) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (htmp : d.stacks 31 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 31 0 1
    hsd hst htd (by decide) d.regs d.stacks htmp)

theorem peek_eval (d : Data) : Eval peek 1 d (peeked d) :=
  .base (.atom _ _)

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src : Fin 40) (h : src ≠ 37) :
    Function.Injective (framePorts src) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

theorem emitFrame_eval (d : Data) (src : Fin 40) (h : src ≠ 37)
    (bits : List Bool) (hs : d.stacks src = bits.reverse) :
    ∃ rr, Eval (emitFrame src) (4 * bits.length + 6) d
      ⟨rr, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ := by
  obtain ⟨rf, ht⟩ := Program.frameEmit_trace bits (d.stacks 37) (d.regs ∘ frameRegs)
  let b := Program.frameData rf [] (Encoding.frame bits ++ d.stacks 37)
  let final := embedState frameRegs (framePorts src) d b
  have ha : embedState frameRegs (framePorts src) d
      (Program.frameData (d.regs ∘ frameRegs) bits.reverse (d.stacks 37)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective (framePorts_injective src h)
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [framePorts, Program.frameData, hs]
    · intros; rfl
  have hb : final =
      (⟨final.regs, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi37 : i = 37
      · subst i
        have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 1
        simp only [Function.update_self]
        calc
          final.stacks 37 = b.stacks 1 := by
            rw [← show framePorts src (1 : Fin 2) = 37 by rfl]
            exact hh
          _ = Encoding.frame bits ++ d.stacks 37 := by rfl
      · by_cases his : i = src
        · subst i
          have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 0
          simp only [Function.update_of_ne h, Function.update_self]
          calc
            final.stacks src = b.stacks 0 := by
              rw [← show framePorts src (0 : Fin 2) = src by rfl]
              exact hh
            _ = [] := by rfl
        · have hh := embedState_stack_frame frameRegs (framePorts src) d b i (by
            rintro ⟨j, hj⟩; fin_cases j <;> simp_all [framePorts])
          simp only [Function.update_of_ne hi37, Function.update_of_ne his]
          exact hh
  have he := eval_call_lifted Program.frameEmitProgram frameRegs (framePorts src) d
    frameRegs_injective (framePorts_injective src h) ht
  rw [ha] at he
  change Eval (emitFrame src) _ d final at he
  rw [hb] at he
  exact ⟨final.regs, he⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem read_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hout : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state, Program.afterFrame8, hout] using
    Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

theorem transfer_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (Program.transfer8 src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [state, Program.afterTransfer8, hout] using
    Program.transfer8_eval (state regs a) src dst hsd

theorem copy_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have hz : (state regs a).stacks 31 = [] := rfl
  simpa only [state, copied, hout] using
    copy_eval (state regs a) src dst hsd hst htd hz

theorem frame_store (regs : Fin 8 → Bool) (a b : Store) (src : Fin 40)
    (hne : src ≠ 37) (bits : List Bool) (hin : tapes a src = bits.reverse)
    (hout : Function.update (Function.update (tapes a) src []) 37
      (Encoding.frame bits ++ tapes a 37) = tapes b) :
    ∃ rr, Eval (emitFrame src) (4*bits.length+6) (state regs a) (state rr b) := by
  obtain ⟨rr, he⟩ := emitFrame_eval (state regs a) src hne bits hin
  exact ⟨rr, by simpa only [state, hout] using he⟩

theorem prepare_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail accum : List Bool) :
    ∃ rr, Eval prepare
      (6*key.length+9*coeff.length+7*e.scalar.length+7*e.count.length+21)
      (state regs (idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum))
      (state rr (prepared e key coeff tail accum)) := by
  let a := idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum
  let b := {a with source := Encoding.frame coeff ++ tail, key := key.reverse}
  let c := {b with source := tail, coeff := coeff.reverse}
  let d := {c with coeff := [], native := {nativeIdle e with y := coeff}}
  let f := {d with native := {nativeIdle e with x := e.scalar, y := coeff}}
  let g := prepared e key coeff tail accum
  have h1 := read_store regs a b 32 35 (by decide) key (Encoding.frame coeff ++ tail)
    (by simp [a, idle, tapes, List.append_assoc])
    (by funext i; fin_cases i <;> simp [a,b,idle,tapes])
  have h2 := read_store (readRegs regs 0 1 (some false)) b c 32 36 (by decide) coeff tail
    (by rfl)
    (by funext i; fin_cases i <;> simp [b,c,a,idle,tapes])
  have h3 := transfer_store (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false))
    c d 36 9 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,idle,nativeIdle,tapes,transferStacks])
  let r3 := readRegs (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false)) 0 1 none
  have h4 := copy_store r3 d f 34 8 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,idle,nativeIdle,tapes,copyStacks])
  have h5 := copy_store (readRegs r3 0 1 none) f g 39 11 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,g,prepared,idle,nativeIdle,tapes,copyStacks])
  refine ⟨readRegs (readRegs r3 0 1 none) 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,b,c,d,f,idle,tapes] ; omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem emit_eval (regs : Fin 8 → Bool) (e : Environment)
    (key result tail accum : List Bool) :
    ∃ rr, Eval emit (10*key.length+13*result.length+27)
      (state regs (productReady e key result tail accum))
      (state rr (idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum))) := by
  let a := productReady e key result tail accum
  let b := {idle e tail accum with key := key.reverse, coeff := result.reverse}
  let c := {idle e tail accum with coeff := result.reverse, frame := Encoding.frame key}
  let d := {idle e tail ((Encoding.frame key).reverse ++ accum) with coeff := result.reverse}
  let f := {idle e tail ((Encoding.frame key).reverse ++ accum) with frame := Encoding.frame result}
  let g := idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum)
  have h1 := transfer_store regs a b 0 36 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,productReady,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r1,h2⟩ := frame_store (readRegs regs 0 1 none) b c 35 (by decide) key rfl
    (by funext i; fin_cases i <;>
      simp [b,c,idle,nativeIdle,tapes])
  have h3 := transfer_store r1 c d 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [c,d,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r2,h4⟩ := frame_store (readRegs r1 0 1 none) d f 36 (by decide) result rfl
    (by funext i; fin_cases i <;>
      simp [d,f,idle,nativeIdle,tapes])
  have h5 := transfer_store r2 f g 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [f,g,idle,nativeIdle,tapes,transferStacks,
        List.reverse_append,List.append_assoc])
  refine ⟨readRegs r2 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,c,f,productReady,idle,nativeIdle,tapes] ; omega

theorem finish_eval (regs : Fin 8 → Bool) (e : Environment) (output : List Bool) :
    Eval finish (3*output.length+3)
      (state regs (idle e [] output.reverse))
      (state (readRegs regs 0 1 none) {idle e [] [] with output := output}) := by
  have he := transfer_store regs (idle e [] output.reverse)
    {idle e [] [] with output := output} 33 38 (by decide)
    (by funext i; fin_cases i <;>
      simp [idle,nativeIdle,tapes,transferStacks])
  simpa [finish,idle,tapes,Fin.addCases] using he

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem multiply_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ RingScan.serviceMulBudget (baseWidth p t) d + 1, ∃ rr,
      Eval multiply n
        (state regs (prepared (environment p t M cache table scalar degree width)
          key (RingProgram.flat x) tail accum))
        (state rr (productReady (environment p t M cache table scalar degree width)
          key (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum)) := by
  obtain ⟨n,hn,rr,he⟩ := RingScan.serviceMul_eval p t M cache hz table scalar x regs degree width hd hw
  let start := prepared (environment p t M cache table scalar degree width)
    key (RingProgram.flat x) tail accum
  have hh := eval_call_lifted RingScan.serviceMulProgram id nativePorts (state regs start)
    Function.injective_id nativePorts_injective (compiled_halt_trace he 8 0)
  refine ⟨n+1, Nat.add_le_add_right hn 1, rr, ?_⟩
  simpa only [multiply, RingScan.serviceState, embed_native, start, prepared,
    productReady, environment, idle, nativeIdle, valueMul] using hh

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ stepBudget (baseWidth p t) d key.length, ∃ rr,
      Eval step n
        (state regs (idle (environment p t M cache table scalar degree width)
          (Encoding.frame key ++ Encoding.frame (RingProgram.flat x) ++ tail) accum))
        (state rr (idle (environment p t M cache table scalar degree width) tail
          ((Encoding.frame key ++ Encoding.frame
            (RingProgram.flat (valueMul p t M cache table scalar x))).reverse ++ accum))) := by
  let e := environment p t M cache table scalar degree width
  obtain ⟨r1,h1⟩ := prepare_eval regs e key (RingProgram.flat x) tail accum
  obtain ⟨n,hn,r2,h2⟩ := multiply_eval p t M cache hz table scalar x degree width hd hw r1 key tail accum
  obtain ⟨r3,h3⟩ := emit_eval r2 e key
    (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum
  refine ⟨_, ?_, r3, h1.seq (h2.seq h3)⟩
  simp only [RingProgram.flat_length]
  dsimp only [e,environment]
  simp only [RingProgram.flat_length]
  rw [hd]
  unfold stepBudget
  omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) (accum : List Bool) :
    ∃ n ≤ loopBudget key entries, ∃ rr,
      Eval loop n
        (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode key entries) accum)))
        (state rr (idle (environment p t M cache table scalar degree width) []
          ((encode key (scaled p t M cache table scalar entries)).reverse ++ accum))) := by
  induction entries generalizing regs accum with
  | nil =>
      refine ⟨1, le_rfl, readRegs regs 0 7 none, ?_⟩
      have hh : (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode (B := baseWidth p t) (d := d) key []) accum))).regs 7 = false := by
        simp [peeked,state,idle,tapes,readRegs]
      simpa [scaled,encode,Program.encodeDictionary,Program.rawEntries,
        peeked,state,idle,tapes,Fin.addCases] using (Eval.while_false (body := .seq step peek) hh)
  | cons a entries ih =>
      let e := environment p t M cache table scalar degree width
      let input := encode key (a :: entries)
      let recordBits := Encoding.frame (key a.1) ++
        Encoding.frame (RingProgram.flat (valueMul p t M cache table scalar a.2))
      let r0 := readRegs regs 0 7 input.head?
      obtain ⟨n,hn,r1,h1⟩ := step_eval p t M cache hz table scalar a.2 degree width hd hw r0
        (key a.1) (encode key entries) accum
      have hpeek := peek_eval (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum)))
      obtain ⟨m,hm,r2,h2⟩ := ih r1 (recordBits.reverse ++ accum)
      have hflag : (peeked (state regs (idle e input accum))).regs 7 = true := by
        cases hk : key a.1 <;>
          simp [peeked,state,idle,tapes,input,encode_cons,Encoding.frame,hk,readRegs]
      have hstep : Eval step n (peeked (state regs (idle e input accum)))
          (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum))) := by
        simpa [e, recordBits, peeked, state, idle, tapes, Fin.addCases, input, encode_cons, r0] using h1
      have hh := Eval.while_true hflag (hstep.seq hpeek) h2
      refine ⟨n+1+m+1, ?_, r2, ?_⟩
      · simp only [loopBudget]
        omega
      · simpa only [loop, scaled, List.map_cons, encode_cons, List.reverse_append,
          List.append_assoc, e, recordBits, input] using hh

theorem encode_scaled_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (key : K → List Bool) (entries) :
    (encode key (scaled p t M cache table scalar entries)).length = (encode key entries).length := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
      simp only [scaled,List.map_cons,encode_cons,List.length_append,Encoding.length_frame,
        RingProgram.flat_length]
      simpa only [scaled] using congrArg (fun n => (2*(key a.1).length+1)+(2*(d*baseWidth p t)+1)+n) ih

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget key entries, ∃ rr,
      Eval command n
        (state regs (idle (environment p t M cache table scalar degree width) (encode key entries) []))
        (state rr {idle (environment p t M cache table scalar degree width) [] [] with
          output := encode key (scaled p t M cache table scalar entries)}) := by
  let e := environment p t M cache table scalar degree width
  have h1 := peek_eval (state regs (idle e (encode key entries) []))
  obtain ⟨n,hn,r1,h2⟩ := loop_eval p t M cache hz table scalar degree width hd hw key entries regs []
  simp only [List.append_nil] at h2
  have h3 := finish_eval r1 e (encode key (scaled p t M cache table scalar entries))
  refine ⟨_, ?_, _, h1.seq (h2.seq h3)⟩
  rw [encode_scaled_length]
  dsimp only [budget]
  omega

theorem program_runsIn (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (budget key entries + 1)
      ((state regs (idle (environment p t M cache table scalar degree width) (encode key entries) [])).withPC
        (some program.entry))
      ((state rr {idle (environment p t M cache table scalar degree width) [] [] with
        output := encode key (scaled p t M cache table scalar entries)}).withPC none) := by
  obtain ⟨n,hn,rr,he⟩ := command_eval p t M cache hz table scalar degree width hd hw key entries regs
  exact ⟨rr,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 32 38⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem scalePorts_injective : Function.Injective scalePorts := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (d : Data) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst) (htmp : d.stacks 47 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (afterCopy d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 47 0 1 hsd hst htd (by decide) d.regs d.stacks htmp)

theorem clear_eval (d : Data) (src : Fin 56) :
    Eval (clear src) (2*(d.stacks src).length+3) d (afterClear d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa only [clearResult,afterClear,StructuredProgram.State.withPC,Nat.add_assoc] using hh

theorem copy_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst)
    (hs : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterCopy,state,hs] using copy_eval (state regs a) src dst hsd hst htd rfl

theorem clear_state (regs : Fin 8 → Bool) (a b : Store) (src : Fin 56)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterClear,state,hs] using clear_eval (state regs a) src


end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copyRight_eval (regs : Fin 8 → Bool) (a : Store) (he : a.scaleSource = []) :
    Eval (copy 41 32) (7*a.right.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with scaleSource := a.right }) := by
  apply copy_state regs a _ 41 32 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyCoefficient_eval (regs : Fin 8 → Bool) (a : Store) (he : a.scalar = []) :
    Eval (copy 44 34) (7*a.coeff.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with scalar := a.coeff }) := by
  apply copy_state regs a _ 44 34 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem clearScalar_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 34) (2*a.scalar.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with scalar := [] }) := by
  apply clear_state regs a _ 34
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearCoefficient_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 44) (2*a.coeff.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with coeff := [] }) := by
  apply clear_state regs a _ 44
  funext i; fin_cases i <;> simp [clearStacks,tapes]

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem embed_scale (regs rr : Fin 8 → Bool) (a : Store) (source scalar output : List Bool)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    embedState id scalePorts (state regs a)
      (Squarefree.ScaleProgram.state rr { Squarefree.ScaleProgram.idle (scaleEnvironment a scalar) source [] with output := output }) =
    state rr { a with scaleSource := source, scalar := scalar, scaled := output } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [scalePorts,state,tapes,scaleEnvironment,
      Squarefree.ScaleProgram.state,Squarefree.ScaleProgram.tapes,Squarefree.ScaleProgram.idle,
      Squarefree.ScaleProgram.nativeIdle,h0,h1,h2,h3,h4,h27]
  · intro i hi
    fin_cases i <;> first | rfl | (exfalso; apply hi; decide)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem scale_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (he : scaleEnvironment a a.scalar = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hs : a.scaleSource = Squarefree.ScaleProgram.encode key entries) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    ∃ n ≤ Squarefree.ScaleProgram.budget key entries + 1, ∃ rr,
      Eval scale n (state regs a)
        (state rr { a with scaleSource := [], scaled := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries) }) := by
  obtain ⟨rr,n,hn,ht⟩ := Squarefree.ScaleProgram.program_runsIn p t M cache hz table scalar degree width hd hw key entries regs
  have hh := eval_call_lifted Squarefree.ScaleProgram.program id scalePorts (state regs a)
    Function.injective_id scalePorts_injective ht
  rw [←he,←hs] at hh
  have ha : embedState id scalePorts (state regs a)
      (Squarefree.ScaleProgram.state regs (Squarefree.ScaleProgram.idle (scaleEnvironment a a.scalar) a.scaleSource [])) = state regs a := by
    have h := embed_scale regs regs a a.scaleSource a.scalar [] h0 h1 h2 h3 h4 h27
    have hs' : { a with scaleSource := a.scaleSource, scalar := a.scalar, scaled := [] } = a := by cases a; simp_all
    rw [hs'] at h
    exact h
  rw [ha,embed_scale _ _ _ _ _ _ h0 h1 h2 h3 h4 h27] at hh
  exact ⟨n,hn,rr,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem scalePhase_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (he : scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hr : a.right = Squarefree.ScaleProgram.encode key entries)
    (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    ∃ n ≤ 7*a.right.length+11*a.coeff.length+Squarefree.ScaleProgram.budget key entries+17, ∃ rr,
      Eval scalePhase n (state regs a)
        (state rr {a with coeff := [], scaled := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries)}) := by
  let b : Store := {a with scaleSource := a.right}
  let c : Store := {b with scalar := b.coeff}
  let output := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries)
  let f : Store := {c with scaleSource := [], scaled := output}
  let g : Store := {f with scalar := []}
  have hcopyB := copyRight_eval regs a hs
  have hcopyC := copyCoefficient_eval (readRegs regs 0 1 none) b hc
  obtain ⟨n,hn,rr,hscale⟩ := scale_eval p t M cache hz table scalar degree width hd hw key entries
    (readRegs (readRegs regs 0 1 none) 0 1 none) c he hr ho h0 h1 h2 h3 h4 h27
  have hclearC := clearScalar_eval rr f
  have hclearInput := clearCoefficient_eval (readRegs rr 0 1 none) g
  have run := hcopyB.seq (hcopyC.seq (hscale.seq (hclearC.seq hclearInput)))
  refine ⟨_,?_,readRegs (readRegs rr 0 1 none) 0 1 none,(by
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (state (readRegs (readRegs rr 0 1 none) 0 1 none))
    cases a
    simp_all [b,c,f,g,output])⟩
  dsimp [b,c,f,g,output] at hn ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval_oai.{u_1}
