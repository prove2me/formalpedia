-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:18:45.537118+00:00
-- url     : https://prove2.me/submissions/2ba705ac-b449-40b6-afef-30a87a843ba4

import Mathlib
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S084

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Eval command 5 (state regs (frame a b++tail)) (state ![false,true,a,b] tail) := by
  let d := state regs (frame a b++tail)
  let d1 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d
  let d2 := (StructuredProgram.Atom.pop (0 : Fin 1) (2 : Fin 4) 1).eval d1
  let d3 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d2
  let d4 := (StructuredProgram.Atom.pop (0 : Fin 1) (3 : Fin 4) 1).eval d3
  let d5 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d4
  have h : Eval command 5 d d5 :=
    (Eval.base (.atom (.pop 0 0 1) d)).seq
      ((Eval.base (.atom (.pop 0 2 1) d1)).seq
        ((Eval.base (.atom (.pop 0 0 1) d2)).seq
          ((Eval.base (.atom (.pop 0 3 1) d3)).seq (Eval.base (.atom (.pop 0 0 1) d4)))))
  have he : d5=state ![false,true,a,b] tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext i
      fin_cases i ; simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
  exact he ▸ h

theorem program_trace (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Trace program 6 ((state regs (frame a b++tail)).withPC (some program.entry))
      ((state ![false,true,a,b] tail).withPC none) :=
  compiled_halt_trace (command_eval regs a b tail) 0 0

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native operations for adding a Cayley shift to a vertex word.
The Boolean mode chooses left or right incidence; shift frames are consumed
on both sides so each iteration advances exactly one local port. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem cellRegisters_injective : Function.Injective cellRegisters := Fin.castAdd_injective _ _
theorem cellStacks_injective : Function.Injective cellStacks := by intro i j h; fin_cases i; fin_cases j; rfl

theorem cell_eval (regs : Fin 8 → Bool) (b : Bool) (tail vertex accum out : List Bool) :
    Eval cell 6 (state regs (Cell.frame b false++tail) vertex accum out)
      (state (cellRegs regs b) tail vertex accum out) := by
  let d := state regs (Cell.frame b false++tail) vertex accum out
  have hs : embedState cellRegisters cellStacks d
      (Cell.state (regs ∘ cellRegisters) (Cell.frame b false++tail))=d := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i; rfl
    · intro i hi; rfl
  have hf : embedState cellRegisters cellStacks d
      (Cell.state ![false,true,b,false] tail)=state (cellRegs regs b) tail vertex accum out := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellRegisters] using h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,by simpa [cellRegisters] using h.symm⟩
      have h2 : i≠2 := fun h => hi ⟨2,by simpa [cellRegisters] using h.symm⟩
      have h3 : i≠3 := fun h => hi ⟨3,by simpa [cellRegisters] using h.symm⟩
      fin_cases i <;> simp_all [cellRegs,state,d]
    · intro i; fin_cases i; rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellStacks] using h.symm⟩
      fin_cases i <;> simp_all [state,d]
  have he := eval_call_lifted Cell.program cellRegisters cellStacks d
    cellRegisters_injective cellStacks_injective (Cell.program_trace (regs ∘ cellRegisters) b false tail)
  rw [hs,hf] at he
  exact he

theorem combine_eval (regs : Fin 8 → Bool) (side v shift : Bool)
    (hside : regs 7=side) (hv : regs 4=v) (hs : regs 2=shift)
    (source vertex accum out : List Bool) :
    Eval combine 2 (state regs source vertex accum out)
      (state (Function.update regs 4 (bit side v shift)) source vertex accum out) := by
  cases side
  · apply Eval.ite_false hside
    simpa [bit,hv,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr]
      using (Eval.base (StructuredProgram.Eval.atom (.copy 4 4)
      (state regs source vertex accum out)))
  · apply Eval.ite_true hside
    simpa [bit,hv,hs,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr]
      using (Eval.base (StructuredProgram.Eval.atom (.bxor 4 4 2)
      (state regs source vertex accum out)))

theorem step_eval (regs : Fin 8 → Bool) (side v shift : Bool)
    (hside : regs 7=side) (hv : regs 4=v)
    (tail vertex accum out : List Bool) :
    ∃ rf, rf 7=side ∧ Eval step 9
      (state regs (Cell.frame shift false++tail) vertex accum out)
      (state rf tail vertex (bit side v shift::accum) out) := by
  have h1 := cell_eval regs shift tail vertex accum out
  let r1 := cellRegs regs shift
  have h2 := combine_eval r1 side v shift hside hv rfl tail vertex accum out
  let r2 := Function.update r1 4 (bit side v shift)
  have h3 : Eval (.base (.atom (.push 2 4))) 1 (state r2 tail vertex accum out)
      (state r2 tail vertex (bit side v shift::accum) out) := by
    have hst : Function.update (![tail,vertex,accum,out] : Fin 4 → List Bool) 2
        (bit side v shift::accum)=![tail,vertex,bit side v shift::accum,out] := by
      first | done | (funext i; fin_cases i <;> simp)
    simpa [state,r2,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
      using (Eval.base (StructuredProgram.Eval.atom (.push 2 4)
      (state r2 tail vertex accum out)))
  exact ⟨r2,by simp [r2,r1,cellRegs,hside],h1.seq (h2.seq h3)⟩

theorem pop_cons (regs : Fin 8 → Bool) (v : Bool) (source vertex accum out : List Bool) :
    Eval pop 1 (state regs source (v::vertex) accum out)
      (state (readRegs regs 4 5 (some v)) source vertex accum out) := by
  have hst : Function.update (![source,v::vertex,accum,out] : Fin 4 → List Bool) 1
      vertex=![source,vertex,accum,out] := by
    first | done | (funext i; fin_cases i <;> simp)
  simpa [state,pop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
    using (Eval.base (StructuredProgram.Eval.atom (.pop 1 4 5)
    (state regs source (v::vertex) accum out)))

theorem pop_nil (regs : Fin 8 → Bool) (source accum out : List Bool) :
    Eval pop 1 (state regs source [] accum out)
      (state (readRegs regs 4 5 none) source [] accum out) := by
  have hst : Function.update (![source,[],accum,out] : Fin 4 → List Bool) 1
      []=![source,[],accum,out] := by
    first | done | (funext i; fin_cases i <;> simp)
  simpa [state,pop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hst]
    using (Eval.base (StructuredProgram.Eval.atom (.pop 1 4 5)
    (state regs source [] accum out)))

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem split_seq {c d : Cmd 8 4} {n : ℕ} {a b : Data}
    (h : Eval (.seq c d) n a b) :
    ∃ nc nd middle, n=nc+nd ∧ Eval c nc a middle ∧ Eval d nd middle b := by
  cases h with
  | seq hc hd => exact ⟨_,_,_,rfl,hc,hd⟩

theorem loop_eval (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail accum out : List Bool) :
    ∃ rf, rf 7=side ∧ Eval loop (11*pairs.length+2)
      (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) accum out)
      (state rf tail [] ((result side pairs).reverse++accum) out) := by
  induction pairs generalizing regs accum with
  | nil =>
    let rr := readRegs regs 4 5 none
    refine ⟨rr,by simpa [rr,readRegs] using hside,?_⟩
    have h := (pop_nil regs tail accum out).seq (Eval.while_false (body := .seq step pop)
      (show (state rr tail [] accum out).regs 5=false by simp [state,rr,readRegs]))
    simpa [loop,frames,result] using h
  | cons p pairs ih =>
    rcases p with ⟨v,s⟩
    let source := frames (pairs.map Prod.snd)++tail
    let rr := readRegs regs 4 5 (some v)
    have hp := pop_cons regs v (Cell.frame s false++source) (pairs.map Prod.fst) accum out
    obtain ⟨rs,hrs,hs⟩ := step_eval rr side v s (by simpa [rr,readRegs] using hside)
      (by simp [rr,readRegs]) source (pairs.map Prod.fst) accum out
    obtain ⟨rf,hrf,hi⟩ := ih rs hrs (bit side v s::accum)
    obtain ⟨tn,tw,between,hncost,hn,hw⟩ := split_seq hi
    refine ⟨rf,hrf,?_⟩
    have hg : (state rr (Cell.frame s false++source) (pairs.map Prod.fst) accum out).regs 5=true := by
      simp [state,rr,readRegs]
    have he := hp.seq (Eval.while_true hg (hs.seq hn) hw)
    convert he using 1 <;>
      simp_all [frames,source,result,List.append_assoc,List.reverse_cons] ; omega

theorem command_eval_oai (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
    ∃ rf, rf 7=side ∧ Eval command (14*pairs.length+5)
      (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) [] [])
      (state rf tail [] [] (result side pairs)) := by
  obtain ⟨rr,hrr,hl⟩ := loop_eval pairs side regs hside tail [] []
  have ht := Subexp.TupleProgram.transfer_eval (2 : Fin 4) 3 (0 : Fin 8) 1
    (by decide) (by decide) (state rr tail [] ((result side pairs).reverse++[]) [])
  let rf := readRegs rr 0 1 none
  refine ⟨rf,by simpa [rf,readRegs] using hrr,?_⟩
  have he := hl.seq ht
  convert he using 1
  · simp [state,result]
    omega
  · apply congrArg (StructuredProgram.State.mk rf)
    funext i
    fin_cases i <;> simp [state,StackRoutines.transferStacks,result]

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval_oai
