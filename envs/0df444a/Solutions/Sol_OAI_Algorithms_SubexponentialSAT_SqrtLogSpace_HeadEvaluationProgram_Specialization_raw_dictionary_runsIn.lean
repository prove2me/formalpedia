-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:17:22.314476+00:00
-- url     : https://prove2.me/submissions/1e544fb6-f7e9-4b5b-b3b4-ee68f18cd4dd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProjectionProgram_hit_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scan used by exact-support projection: consume a mask while
copying its bits and an equally long zero mask to reversed accumulators. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem body_eval (regs : Fin 3 → Bool) (b : Bool) (source copy zeros : List Bool) :
    ∃ rf, Eval body 5 (maskData regs (b::source) copy zeros)
      (ready rf source (b::copy) (false::zeros)) := by
  let d := maskData regs (b::source) copy zeros
  let d1 := (Atom.pop (0:Fin 3) (0:Fin 3) 1).eval d
  let d2 := (Atom.push (1:Fin 3) (0:Fin 3)).eval d1
  let d3 := (Atom.set (2:Fin 3) false).eval d2
  let d4 := (Atom.push (2:Fin 3) (2:Fin 3)).eval d3
  refine ⟨d3.regs, ?_⟩
  have h := (Eval.atom (Atom.pop (0:Fin 3) (0:Fin 3) 1) d).seq
    ((Eval.atom (Atom.push (1:Fin 3) (0:Fin 3)) d1).seq
    ((Eval.atom (Atom.set (2:Fin 3) false) d2).seq
    ((Eval.atom (Atom.push (2:Fin 3) (2:Fin 3)) d3).seq
     (Eval.atom (Atom.peek (0:Fin 3) (0:Fin 3) 1) d4))))
  convert h using 1 ;
    simp [d,d1,d2,d3,d4,ready,maskData,Atom.eval,Atom.instr,
      State.ofCfg,execInstr,readRegs,Function.update] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem loop_eval (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Eval loop (6*source.length+1) (ready regs source copy zeros)
      (maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)) := by
  induction source generalizing copy zeros regs with
  | nil =>
      refine ⟨(ready regs [] copy zeros).regs, ?_⟩
      simpa [loop,ready,maskData] using
        (Eval.while_false (body:=body) (ready_guard regs [] copy zeros))
  | cons b source ih =>
      obtain ⟨mid,hm⟩ := body_eval (ready regs (b::source) copy zeros).regs b source copy zeros
      obtain ⟨rf,hf⟩ := ih (b::copy) (false::zeros) mid
      refine ⟨rf,?_⟩
      have h := Eval.while_true
        (by simp : (ready regs (b::source) copy zeros).regs 1 = true) hm hf
      have ht : 5+(6*source.length+1)+1 = 6*(b::source).length+1 := by simp;omega
      rw [ht] at h
      have hz : List.replicate source.length false ++ false :: zeros =
          false :: (List.replicate source.length false ++ zeros) := by
        simpa [List.replicate_add,List.append_assoc] using
          congrArg (fun n => List.replicate n false ++ zeros) (Nat.add_comm source.length 1)
      simpa [loop,ready,maskData,List.reverse_cons,List.append_assoc,
        List.replicate_succ,hz] using h

theorem scan_eval (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Eval scan (6*source.length+2) (maskData regs source copy zeros)
      (maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)) := by
  obtain ⟨rf,hf⟩ := loop_eval source copy zeros regs
  refine ⟨rf,?_⟩
  have hp : Eval (.atom (.peek 0 0 1)) 1 (maskData regs source copy zeros)
      (ready regs source copy zeros) := Eval.atom _ _
  have ht : 1+(6*source.length+1) = 6*source.length+2 := by omega
  simpa only [scan,ht] using hp.seq hf

theorem scan_trace (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Trace scanProgram (6*source.length+3)
      ((maskData regs source copy zeros).withPC (some scanProgram.entry))
      ((maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)).withPC none) := by
  obtain ⟨rf,h⟩ := scan_eval source copy zeros regs
  exact ⟨rf,by simpa [scanProgram,Nat.add_assoc] using compiled_halt_trace h 0 1⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem natRegs_injective : Function.Injective natRegs := Fin.castAdd_injective _ _
theorem natPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (natPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [natPorts, ParserProgram.pair]

theorem readNat_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst)
    (n : ℕ) (rest : List Bool) (hin : d.stacks src = Encoding.encodeNat n ++ rest) :
    Eval (readNat src dst) (4 * n + 4) d (afterNat d src dst n rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.encodeNat n ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (List.replicate n true ++ d.stacks dst)⟩
  have ha : embedState natRegs (natPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState natRegs (natPorts src dst) d b = afterNat d src dst n rest := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterNat, natRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [natRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [natRegs] using h.symm⟩
      simp [afterNat, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterNat, natPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [natPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [natPorts] using h.symm⟩
      simp [afterNat, hsrc, hdst]
  have ht : Trace ParserProgram.natProgram (4 * n + 4)
      (a.withPC (some ParserProgram.natProgram.entry)) (b.withPC none) :=
    ParserProgram.nat_trace n rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.natProgram natRegs
    (natPorts src dst) d natRegs_injective (natPorts_injective src dst hsd) ht
  simpa only [ha,hb,readNat] using h

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem clearAt_eval {s : ℕ} (d : State 5 s) (src : Fin s) :
    Eval (clearAt src) (2*(d.stacks src).length+3) d (clearedAt d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clearedAt,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

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

theorem readFrame_eval (d : State 5 10) (src dst : Fin 10) (hsd : src ≠ dst)
    (bits rest : List Bool) (hi : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame src dst) (6*bits.length+4) d (afterFrame d src dst bits rest) := by
  have hr : Function.Injective readRegsMap := Fin.castAdd_injective _ _
  have hp : Function.Injective (readPorts src dst) := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [readPorts,ParserProgram.pair]
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits++rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse++d.stacks dst)⟩
  have ha : embedState readRegsMap (readPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ hr hp
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hi
      · rfl
    · intros; rfl
  have hb : embedState readRegsMap (readPorts src dst) d b = afterFrame d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ hr hp
    · intro i; fin_cases i <;> simp [afterFrame,readRegsMap,readRegs,b,ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,by simpa [readRegsMap] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1,by simpa [readRegsMap] using h.symm⟩
      simp [afterFrame,readRegs,h0,h1]
    · intro i; fin_cases i <;> simp [afterFrame,readPorts,ParserProgram.pair,b,hsd]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0,by simpa [readPorts] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨1,by simpa [readPorts] using h.symm⟩
      simp [afterFrame,hs,hd]
  have ht : Trace ParserProgram.frameProgram (6*bits.length+4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram readRegsMap (readPorts src dst) d hr hp ht
  simpa only [ha,hb,readFrame] using h

theorem transfer_machine (regs : Fin 5 → Bool) (a b : Tape) (src dst : Fin 10)
    (hsd : src ≠ dst) (hs : StackRoutines.transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0:Fin 5) 1 hsd (by decide) regs (tapes a)
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transfer,machine,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc,hs] using hh

theorem clear_machine (regs : Fin 5 → Bool) (a b : Tape) (src : Fin 10)
    (hs : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa [clear,machine,Squarefree.Program.clearedAt,hs] using
    Squarefree.Program.clearAt_eval (machine regs a) src

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem maskPorts_injective : Function.Injective maskPorts := by decide

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

/-- The mask service preserves all tape fields outside work/key/newkey. -/
theorem scanMask_eval (regs : Fin 5 → Bool) (a : Tape) :
    ∃ rf, Eval scanMask (6*a.work.length+3) (machine regs a)
      (machine rf {a with work:=[],key:=a.work.reverse++a.key, newkey:=List.replicate a.work.length false++a.newkey}) := by
  obtain ⟨rr,hh⟩ := scan_trace a.work a.key a.newkey (regs ∘ smallRegs)
  let b := maskData rr [] (a.work.reverse++a.key) (List.replicate a.work.length false++a.newkey)
  let rf := (embedState smallRegs maskPorts (machine regs a) b).regs
  have ha : embedState smallRegs maskPorts (machine regs a)
      (maskData (regs ∘ smallRegs) a.work a.key a.newkey) = machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective maskPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState smallRegs maskPorts (machine regs a) b =
      machine rf {a with work:=[],key:=a.work.reverse++a.key, newkey:=List.replicate a.work.length false++a.newkey} := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective maskPorts_injective
    · intro i; exact embedState_register smallRegs maskPorts (machine regs a) b smallRegs_injective i
    · intro i hi; exact embedState_register_frame smallRegs maskPorts (machine regs a) b i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [maskPorts,machine,tapes,Fin.exists_fin_succ]
  have h := eval_call_lifted scanProgram smallRegs maskPorts (machine regs a)
    smallRegs_injective maskPorts_injective hh
  exact ⟨rf,by simpa only [ha,hb,scanMask,b] using h⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Copy one unary field to the reversed output key, including its delimiter. -/
theorem header_eval (regs : Fin 5 → Bool) (a : Tape) (n : ℕ) (rest : List Bool)
    (hw : a.work = Encoding.encodeNat n ++ rest) :
    ∃ rf, Eval header (4*n+5) (machine regs a)
      (machine rf {a with work:=rest,newkey:=(Encoding.encodeNat n).reverse++a.newkey}) := by
  let r := readRegs regs (0:Fin 5) 1 (some false)
  let b : Tape := {a with work:=rest,newkey:=List.replicate n true++a.newkey}
  have h := Squarefree.Program.readNat_eval (machine regs a) 4 5 (by decide) n rest hw
  have h' : Eval (Squarefree.Program.readNat 4 5) (4*n+4)
      (machine regs a) (machine r b) := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [machine,tapes,b]
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (5:Fin 10) (0:Fin 5))
    (machine r b))
  have hp' : Eval (.base (.atom (.push 5 0))) 1 (machine r b)
      (machine r {a with work:=rest,newkey:=(Encoding.encodeNat n).reverse++a.newkey}) := by
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [machine,tapes,b,r,Encoding.encodeNat,
          StructuredProgram.Atom.instr,execInstr,readRegs,List.reverse_append]
  refine ⟨r,?_⟩
  simpa [header] using h'.seq hp'

/-- The key rewriter reads the two unary fields and then scans precisely the mask. -/
theorem rewriteKey_eval (regs : Fin 5 → Bool) (a : Tape) (u z : ℕ) (mask : List Bool)
    (hk : a.key = (Encoding.encodeNat u++Encoding.encodeNat z++mask).reverse)
    (hw : a.work = []) (hn : a.newkey = []) :
    ∃ rf, Eval rewriteKey
      (3*(Encoding.encodeNat u++Encoding.encodeNat z++mask).length+4*u+4*z+6*mask.length+16)
      (machine regs a)
      (machine rf {a with work:=[],key:=mask.reverse, newkey:=(Encoding.encodeNat u++Encoding.encodeNat z++List.replicate mask.length false).reverse}) := by
  let a₁ : Tape := {a with key:=[],work:=Encoding.encodeNat u++Encoding.encodeNat z++mask}
  let r₁ := readRegs regs (0:Fin 5) 1 none
  have h₁ := transfer_machine regs a a₁ 2 4 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,a₁,hk,hw])
  obtain ⟨r₂,h₂⟩ := header_eval r₁ a₁ u (Encoding.encodeNat z++mask) (by simp [a₁,List.append_assoc])
  let a₂ : Tape := {a₁ with work:=Encoding.encodeNat z++mask,newkey:=(Encoding.encodeNat u).reverse++a₁.newkey}
  obtain ⟨r₃,h₃⟩ := header_eval r₂ a₂ z mask rfl
  let a₃ : Tape := {a₂ with work:=mask,newkey:=(Encoding.encodeNat z).reverse++a₂.newkey}
  obtain ⟨rf,h₄⟩ := scanMask_eval r₃ a₃
  have h₂' : Eval header (4*u+5) (machine r₁ a₁) (machine r₂ a₂) := h₂
  have h₃' : Eval header (4*z+5) (machine r₂ a₂) (machine r₃ a₃) := h₃
  have h₄' : Eval scanMask (6*mask.length+3) (machine r₃ a₃)
      (machine rf {a with work:=[],key:=mask.reverse, newkey:=(Encoding.encodeNat u++Encoding.encodeNat z++List.replicate mask.length false).reverse}) := by
    simpa [a₃,a₂,a₁,hn,List.reverse_append,List.append_assoc] using h₄
  refine ⟨rf,?_⟩
  have he := h₁.seq (h₂'.seq (h₃'.seq h₄'))
  convert he using 1 ; simp [tapes,hk,List.length_reverse] ; omega

theorem miss_eval (regs : Fin 5 → Bool) (a : Tape) :
    ∃ rf, Eval miss (2*a.coeff.length+3+(2*a.newkey.length+3))
      (machine regs a) (machine rf {a with coeff:=[],newkey:=[]}) := by
  let b : Tape := {a with coeff:=[]}
  let c : Tape := {a with coeff:=[],newkey:=[]}
  have h₁ := clear_machine regs a b 3 (by funext i; fin_cases i <;> simp [tapes,b])
  have h₂ := clear_machine (readRegs regs 0 1 none) b c 5
    (by funext i; fin_cases i <;> simp [tapes,b,c])
  refine ⟨readRegs (readRegs regs 0 1 none) 0 1 none,?_⟩
  simpa [miss,tapes,b,c] using h₁.seq h₂

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem read_key (regs : Fin 5 → Bool) (u z : ℕ) (mask coeff rest query output : List Bool) :
    Eval (readFrame 0 2) (6*(keyBits u z mask).length+4)
      (machine regs (clean (recordBits u z mask coeff++rest) query output))
      (machine (readRegs regs 0 1 (some false))
        {clean (Encoding.frame coeff++rest) query output with key:=(keyBits u z mask).reverse}) := by
  have h := readFrame_eval (machine regs (clean (recordBits u z mask coeff++rest) query output))
    0 2 (by decide) (keyBits u z mask) (Encoding.frame coeff++rest)
    (by simp [machine,tapes,clean,recordBits,List.append_assoc])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [machine,tapes,clean]

theorem read_coeff (regs : Fin 5 → Bool) (key coeff rest query output : List Bool) :
    Eval (readFrame 0 3) (6*coeff.length+4)
      (machine regs {clean (Encoding.frame coeff++rest) query output with key:=key})
      (machine (readRegs regs 0 1 (some false))
        {clean rest query output with key:=key,coeff:=coeff.reverse}) := by
  have h := readFrame_eval
    (machine regs {clean (Encoding.frame coeff++rest) query output with key:=key})
    0 3 (by decide) coeff rest rfl
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [machine,tapes,clean]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem readyRecords_cons_guard (regs : Fin 5 → Bool) (e : Entry)
    (es : List Entry) (query output : List Bool) :
    (readyRecords regs (raw (e::es)) query output).regs 3 = true := by
  cases hkey : keyBits e.u e.z e.mask <;>
    simp [readyRecords,machine,readRegs,raw,Entry.bits,recordBits,hkey,Encoding.frame]

theorem loopBudget_bound (query : List Bool) (es : List Entry) :
    loopBudget query es ≤ 102*((raw es).length+(query.length+1)*es.length)+1 := by
  induction es with
  | nil => simp [loopBudget,raw]
  | cons e es ih =>
      simp only [loopBudget,raw,List.length_append,List.length_cons]
      nlinarith

theorem raw_count (es : List Entry) : es.length ≤ (raw es).length := by
  induction es with
  | nil => simp [raw]
  | cons e es ih =>
      simp only [raw,List.length_append,List.length_cons]
      have he : 1 ≤ e.bits.length := by simp [Entry.bits,recordBits_length]
      omega

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

theorem raw_ofIndex {n : ℕ} (l : List (Index (Fin n) × List Bool)) :
    raw (l.map ofIndex) = Squarefree.Program.rawEntries
      (l.map fun a => (encodeIndex a.1,a.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [raw,Squarefree.Program.rawEntries,ofIndex,Entry.bits,
      recordBits,keyBits,encodeIndex,ih,List.append_assoc]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

theorem body_eval (r : Fin 5 → Bool) (b q : Bool) (bs qs saved : List Bool) :
    ∃ rf, Eval body 7 (data r (b::bs) (q::qs) saved)
      (ready rf bs qs (q::saved)) ∧ rf 4 = (r 4 && (!b || q)) := by
  let d0 := data r (b::bs) (q::qs) saved
  let d1 := (Atom.pop (0:Fin 3) (0:Fin 5) 1).eval d0
  let d2 := (Atom.pop (1:Fin 3) (2:Fin 5) 3).eval d1
  let d3 := (Atom.push (2:Fin 3) (2:Fin 5)).eval d2
  let d4 := (Atom.bnot (0:Fin 5) 0).eval d3
  let d5 := (Atom.bor (0:Fin 5) 0 2).eval d4
  let d6 := (Atom.band (4:Fin 5) 4 0).eval d5
  have h := (Eval.atom (Atom.pop (0:Fin 3) (0:Fin 5) 1) d0).seq
    ((Eval.atom (Atom.pop (1:Fin 3) (2:Fin 5) 3) d1).seq
    ((Eval.atom (Atom.push (2:Fin 3) (2:Fin 5)) d2).seq
    ((Eval.atom (Atom.bnot (0:Fin 5) 0) d3).seq
    ((Eval.atom (Atom.bor (0:Fin 5) 0 2) d4).seq
    ((Eval.atom (Atom.band (4:Fin 5) 4 0) d5).seq
    (Eval.atom (Atom.peek (0:Fin 3) (0:Fin 5) 1) d6))))))
  refine ⟨d6.regs,?_,?_⟩
  · convert h using 1
    · rfl
    · apply congrArg₂ State.mk
      · rfl
      · funext i; fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,data,
          Atom.eval,Atom.instr,State.ofCfg,execInstr,readRegs]
  · simp [d0,d1,d2,d3,d4,d5,d6,data,Atom.eval,Atom.instr,
      State.ofCfg,execInstr,readRegs]

theorem loop_eval (mask query saved : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length = query.length) :
    ∃ rf, Eval loop (8*mask.length+1) (ready r mask query saved)
      (data rf [] [] (query.reverse++saved)) ∧ rf 4 = (r 4 && below mask query) := by
  induction mask generalizing query saved r with
  | nil =>
    have hq : query=[] := List.length_eq_zero_iff.mp hl.symm
    subst query
    refine ⟨(ready r [] [] saved).regs,?_,?_⟩
    · simpa [loop,ready,data] using
        (Eval.while_false (body:=body) (by simp [ready,data,readRegs] :
          (ready r [] [] saved).regs 1 = false))
    · simp [ready,data,readRegs,below]
  | cons b bs ih =>
    cases query with
    | nil => simp at hl
    | cons q qs =>
      obtain ⟨rb,hb,hv⟩ := body_eval (readRegs r 0 1 (some b)) b q bs qs saved
      obtain ⟨rf,hf,hout⟩ := ih qs (q::saved) rb (by simpa using hl)
      refine ⟨rf,?_,?_⟩
      · have hh := Eval.while_true (body:=body)
          (by simp [ready,data,readRegs] : (ready r (b::bs) (q::qs) saved).regs 1=true) hb hf
        convert hh using 1 <;> simp [loop,data,List.reverse_cons,List.append_assoc]
        omega
      · rw [hout,hv]
        simp [readRegs,below,Bool.and_assoc]

theorem command_eval (mask query : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length = query.length) :
    ∃ rf, Eval command (8*mask.length+3) (data r mask query [])
      (data rf [] [] query.reverse) ∧ rf 4 = below mask query := by
  let r1 := Function.update r 4 true
  have hs : Eval (.atom (.set 4 true)) 1 (data r mask query [])
      (data r1 mask query []) := Eval.atom _ _
  have hp : Eval (.atom (.peek 0 0 1)) 1 (data r1 mask query [])
      (ready r1 mask query []) := Eval.atom _ _
  obtain ⟨rf,hf,hv⟩ := loop_eval mask query [] r1 hl
  refine ⟨rf,?_,by simpa [r1] using hv⟩
  convert hs.seq (hp.seq hf) using 1
  · rfl
  · omega
  · simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

theorem below_eq_true (mask query : List Bool) (hl : mask.length=query.length) :
    below mask query = true ↔ List.Forall₂ (fun b q => b=true → q=true) mask query := by
  induction mask generalizing query with
  | nil =>
    have hq : query=[] := List.length_eq_zero_iff.mp hl.symm
    subst query
    simp [below]
  | cons b bs ih =>
    cases query with
    | nil => simp at hl
    | cons q qs =>
      rw [below,List.forall₂_cons]
      simp only [List.headD_cons,List.tail_cons]
      rw [Bool.and_eq_true,ih qs (by simpa using hl)]
      cases b <;> cases q <;> simp

theorem below_reverse (mask query : List Bool) (hl : mask.length=query.length) :
    below mask.reverse query.reverse = below mask query := by
  apply Bool.eq_iff_iff.mpr
  rw [below_eq_true _ _ (by simpa using hl),below_eq_true _ _ hl,List.forall₂_reverse_iff]

theorem program_trace (mask query : List Bool) (r : Fin 5 → Bool)
    (hl : mask.length=query.length) :
    ∃ rf, Trace program (8*mask.length+4)
      ((data r mask query []).withPC (some program.entry))
      ((data rf [] [] query.reverse).withPC none) ∧ rf 4=below mask query := by
  obtain ⟨rf,hf,hv⟩ := command_eval mask query r hl
  exact ⟨rf,by simpa [program,Nat.add_assoc] using compiled_halt_trace hf 0 2,hv⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram

theorem subsetPorts_injective : Function.Injective subsetPorts := by decide

theorem compare_eval (regs : Fin 5 → Bool) (a : Tape) (key query : List Bool)
    (hk : a.key=key.reverse) (hq : a.target=query.reverse) (ht : a.tmp=[])
    (hl : key.length=query.length) :
    ∃ time ≤ 11*key.length+9*query.length+21, ∃ rf,
      Eval compare time (machine regs a) (machine rf {a with key:=[],tmp:=[]}) ∧
      rf 4 = Subset.below key query := by
  obtain ⟨rr,hh,hv⟩ := Subset.program_trace key.reverse query.reverse regs (by simpa using hl)
  let b := Subset.data rr [] [] query
  have ha : embedState id subsetPorts (machine regs a)
      (Subset.data regs key.reverse query.reverse []) = machine regs a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id subsetPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [Subset.data,subsetPorts,machine,tapes,hk,hq,ht]
    · intros; rfl
  have hb : embedState id subsetPorts (machine regs a) b =
      machine rr {a with key:=[],target:=[],tmp:=query} := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id subsetPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [subsetPorts,machine,tapes,Fin.exists_fin_succ]
  have hs := eval_call_lifted Subset.program id subsetPorts (machine regs a)
    Function.injective_id subsetPorts_injective hh
  have hs' : Eval scanSubset (8*key.length+4) (machine regs a)
      (machine rr {a with key:=[],target:=[],tmp:=query}) := by
    simpa only [ha,List.reverse_reverse,List.length_reverse,hb,scanSubset,b] using hs
  have ht' := transfer_machine rr {a with key:=[],target:=[],tmp:=query}
    {a with key:=[],tmp:=[]} 6 1 (by decide) (by
      funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,hq])
  refine ⟨(8*key.length+4)+(3*query.length+3),by omega,readRegs rr 0 1 none,?_,?_⟩
  · simpa [compare,tapes] using hs'.seq ht'
  · simpa [readRegs,Subset.below_reverse _ _ hl] using hv

theorem record_eval (regs : Fin 5 → Bool) (u z : ℕ)
    (mask coeff rest query output : List Bool) (hl : mask.length=query.length) :
    ∃ time ≤ 100*((recordBits u z mask coeff).length+query.length+1), ∃ rf,
      Eval record time
        (machine regs (clean (recordBits u z mask coeff++rest) query output))
        (machine rf (clean rest query
          (if Subset.below mask query = true then (recordBits u z (List.replicate mask.length false) coeff).reverse++output
           else output))) := by
  let r₁ := readRegs regs (0:Fin 5) 1 (some false)
  let r₂ := readRegs r₁ (0:Fin 5) 1 (some false)
  have h₁ := read_key regs u z mask coeff rest query output
  have h₂ := read_coeff r₁ (keyBits u z mask).reverse coeff rest query output
  let a : Tape := {clean rest query output with key:=(keyBits u z mask).reverse,coeff:=coeff.reverse}
  obtain ⟨r₃,h₃⟩ := rewriteKey_eval r₂ a u z mask rfl rfl rfl
  let b : Tape := {clean rest query output with key:=mask.reverse,coeff:=coeff.reverse, newkey:=(keyBits u z (List.replicate mask.length false)).reverse}
  have h₃' : Eval rewriteKey
      (3*(keyBits u z mask).length+4*u+4*z+6*mask.length+16)
      (machine r₂ a) (machine r₃ b) := by
    simpa [a,b,keyBits,clean] using h₃
  obtain ⟨tc,htc,r₄,h₄,hr₄⟩ := compare_eval r₃ b mask query rfl rfl rfl hl
  let c : Tape := {clean rest query output with coeff:=coeff.reverse, newkey:=(keyBits u z (List.replicate mask.length false)).reverse}
  have h₄' : Eval compare tc (machine r₃ b) (machine r₄ c) := by
    simpa [b,c,clean] using h₄
  by_cases heq : Subset.below mask query = true
  · obtain ⟨rf,h₅⟩ := hit_eval r₄ c (keyBits u z (List.replicate mask.length false)) coeff rfl rfl rfl
    have h₅' := Eval.ite_true (yes:=hit) (no:=miss)
      (by simp [machine,hr₄,heq] : (machine r₄ c).regs 4=true) h₅
    have hall := h₁.seq (h₂.seq (h₃'.seq (h₄'.seq h₅')))
    refine ⟨_,?_,rf,by simpa [record,a,c,clean,heq,recordBits,keyBits] using hall⟩
    simp [recordBits_length]
    omega
  · obtain ⟨rf,h₅⟩ := miss_eval r₄ c
    have h₅' := Eval.ite_false (yes:=hit) (no:=miss)
      (by simp [machine,hr₄,heq] : (machine r₄ c).regs 4=false) h₅
    have hall := h₁.seq (h₂.seq (h₃'.seq (h₄'.seq h₅')))
    refine ⟨_,?_,rf,by simpa [record,a,c,clean,heq] using hall⟩
    simp [recordBits_length]
    omega


theorem records_eval (es : List Entry) (regs : Fin 5 → Bool) (query output : List Bool)
    (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ time ≤ loopBudget query es, ∃ rf, Eval records time
      (readyRecords regs (raw es) query output)
      (machine rf (clean [] query ((raw (selected query es)).reverse++output))) := by
  induction es generalizing regs output with
  | nil =>
      refine ⟨1,le_rfl,(readyRecords regs [] query output).regs,?_⟩
      simpa [records,raw,selected,readyRecords,machine,clean] using
        (Eval.while_false (body:=recordBody) (readyRecords_guard regs [] query output))
  | cons e es ih =>
      obtain ⟨tr,htr,rr,hr⟩ := record_eval (readyRecords regs (raw (e::es)) query output).regs
        e.u e.z e.mask e.coeff (raw es) query output (hlen e (by simp))
      let out := if Subset.below e.mask query = true then e.erased.bits.reverse++output else output
      have hr' : Eval record tr (readyRecords regs (raw (e::es)) query output)
          (machine rr (clean (raw es) query out)) := by
        simpa [raw,readyRecords,out,Entry.erased,Entry.bits,machine,clean] using hr
      have hp : Eval (.base (.atom (.peek 0 0 3))) 1
          (machine rr (clean (raw es) query out)) (readyRecords rr (raw es) query out) :=
        Eval.base (StructuredProgram.Eval.atom _ _)
      obtain ⟨tt,htt,rf,ht⟩ := ih rr out (by intro f hf; exact hlen f (List.mem_cons_of_mem e hf))
      have hall := Eval.while_true (body:=recordBody)
        (readyRecords_cons_guard regs e es query output) (hr'.seq hp) ht
      refine ⟨tr+1+tt+1,?_,rf,?_⟩
      · dsimp [loopBudget]; change tr ≤ _ at htr
        simpa [Entry.bits] using (show tr+1+tt+1 ≤
          100*((recordBits e.u e.z e.mask e.coeff).length+query.length+1)+2+loopBudget query es by omega)
      · by_cases h : Subset.below e.mask query = true <;>
          simpa [records,selected,h,raw,out,Entry.bits,Entry.erased,
            List.reverse_append,List.append_assoc] using hall


theorem selected_length (query : List Bool) (es : List Entry) :
    (raw (selected query es)).length ≤ (raw es).length := by
  induction es with
  | nil => simp [selected,raw]
  | cons e es ih =>
      by_cases h : Subset.below e.mask query = true
      · simp [selected,h,raw,Entry.erased,Entry.bits,recordBits_length] at *;omega
      · simp [selected,h,raw];omega


theorem project_eval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ time ≤ 200*((raw es).length+1)*(query.length+2), ∃ rf,
      Eval project time (machine regs {input:=input query es})
        (machine rf {target:=query.reverse,framed:=raw (selected query es)}) := by
  let a : Tape := {input:=input query es}
  let r₁ := readRegs regs (0:Fin 5) 1 (some false)
  have h₁ := readFrame_eval (machine regs a) 0 1 (by decide) query (raw es) rfl
  have h₁' : Eval (readFrame 0 1) (6*query.length+4) (machine regs a)
      (machine r₁ (clean (raw es) query [])) := by
    convert h₁ using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [machine,tapes,a,clean]
  have hp : Eval (.base (.atom (.peek 0 0 3))) 1
      (machine r₁ (clean (raw es) query [])) (readyRecords r₁ (raw es) query []) :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  obtain ⟨tt,htt,rr,ht⟩ := records_eval es r₁ query [] hlen
  let b : Tape := clean [] query (raw (selected query es)).reverse
  have ht' : Eval records tt (readyRecords r₁ (raw es) query []) (machine rr b) := by
    simpa [b] using ht
  let c : Tape := {target:=query.reverse,framed:=raw (selected query es)}
  have hf := transfer_machine rr b c 8 9 (by decide) (by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks,tapes,b,c,clean])
  have hall := h₁'.seq (hp.seq (ht'.seq hf))
  refine ⟨_,?_,readRegs rr 0 1 none,by simpa [project,a,b,c,tapes,clean] using hall⟩
  have hbudget := loopBudget_bound query es
  have hcount := raw_count es
  have hlen := selected_length query es
  have hprod := Nat.mul_le_mul_left (query.length+1) hcount
  nlinarith

/-- Primitive instruction trace with explicit serialized input and output. -/
theorem serializedEval (regs : Fin 5 → Bool) (query : List Bool) (es : List Entry) (hlen : ∀ e ∈ es, e.mask.length=query.length) :
    ∃ rf, RunsIn program (200*((raw es).length+1)*(query.length+2)+1)
      ((machine regs {input:=input query es}).withPC (some program.entry))
      ((machine rf {target:=query.reverse,framed:=raw (selected query es)}).withPC none) := by
  obtain ⟨time,htime,rf,h⟩ := project_eval regs query es hlen
  exact ⟨rf,time+1,Nat.add_le_add_right htime 1,compiled_halt_trace h 0 9⟩


open Squarefree

theorem below_encodeMask {n : ℕ} (s U : Finset (Fin n)) :
    Subset.below (encodeMask s) (encodeMask U) = decide (s ⊆ U) := by
  apply Bool.eq_iff_iff.mpr
  rw [Subset.below_eq_true _ _ (by simp),decide_eq_true_eq]
  constructor
  · intro h v hv
    have hh := h.get (i:=v.val) (by simp) (by simp)
    simp [encodeMask] at hh
    exact hh hv
  · intro h
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have hi' : i<n := by simpa using hi
    simpa [encodeMask] using (show (⟨i,hi'⟩:Fin n) ∈ s → (⟨i,hi'⟩:Fin n) ∈ U from fun hv => h hv)

theorem selected_ofIndex {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) :
    selected (encodeMask U) (l.map ofIndex) =
      (HeadEvaluation.specializeEntries U l).map ofIndex := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a.1.vars ⊆ U <;>
      simp [selected,ofIndex,below_encodeMask,h,HeadEvaluation.specializeEntries,
        ih,Entry.erased,encodeMask_empty]

/-- The fixed native scanner performs immediate Boolean specialization before
any dictionary multiplication. Duplicate numeric keys await normalization. -/
theorem raw_dictionary_runsIn_oai {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program
      (200*((Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+1)*(n+2)+1)
      ((machine regs {input:=Encoding.frame (encodeMask U)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry))
      ((machine rf {target:=(encodeMask U).reverse,framed:=
        Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
          fun a => (encodeIndex a.1,a.2))}).withPC none) := by
  have hl : ∀ e ∈ l.map ofIndex, e.mask.length=(encodeMask U).length := by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    simp [ofIndex]
  simpa [input,raw_ofIndex,selected_ofIndex] using
    serializedEval regs (encodeMask U) (l.map ofIndex) hl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn_oai
