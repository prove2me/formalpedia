-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:53:26.354987+00:00
-- url     : https://prove2.me/submissions/0fcab7e7-1760-4359-90ee-40ceccb1b2e1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S125

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem ExecutesIn.seq {a b : Code} {A B : ℕ} {s t u : Store}
    (ha : ExecutesIn a A s t) (hb : ExecutesIn b B t u) :
    ExecutesIn (.seq a b) (A+B) s u := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesIn.mono {c : Code} {A B : ℕ} {s t : Store}
    (h : ExecutesIn c A s t) (hab : A ≤ B) : ExecutesIn c B s t := by
  intro regs
  obtain ⟨n,rf,hn,he⟩ := h regs
  exact ⟨n,rf,hn.trans hab,he⟩

theorem transfer_run (src dst : Fin 340) (s : Store) (h : src ≠ dst) :
    ExecutesIn (transfer src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.transfer_eval (⟨regs,s⟩ : Data) src dst 0 1 h (by decide)
  exact ⟨_,_,le_rfl,he⟩

theorem copy_run (src dst : Fin 340) (s : Store) (hsd : src ≠ dst)
    (hst : src ≠ 339) (hdt : 339 ≠ dst) (ht : s 339=[]) :
    ExecutesIn (copy src dst) (7*(s src).length+5) s
      (Function.update s dst (s src++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.copy_eval (⟨regs,s⟩ : Data) src dst 339 0 1
    hsd hst hdt (by decide) ht
  refine ⟨_,readRegs regs 0 1 none,le_rfl,?_⟩
  simpa [copy,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using he

theorem clear_run (src : Fin 340) (s : Store) :
    ExecutesIn (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro regs
  have ht := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 regs s) 2 rfl rfl
  refine ⟨_,readRegs regs 0 1 none,le_rfl,Eval.call _ ?_⟩
  simpa [StackRoutines.clearProgram,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,Nat.add_assoc] using ht

theorem push_run (dst : Fin 340) (b : Bool) (s : Store) :
    ExecutesIn (push dst b) 2 s (Function.update s dst (b::s dst)) := by
  intro regs
  exact ⟨2,Function.update regs 0 b,le_rfl,Subexp.TupleProgram.pushConst_eval dst 0 b ⟨regs,s⟩⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem frameRegisters_injective : Function.Injective frameRegisters := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by decide

theorem frameRow_run (s : Store) :
    ExecutesIn frameRow (4*(s 330).length+6) s
      (Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334)) := by
  intro regs
  let a : Data := ⟨regs,s⟩
  let small := projectState frameRegisters frameStacks a
  obtain ⟨rf,ht⟩ := Squarefree.Program.frameEmit_trace (s 330).reverse (s 334) small.regs
  have heq : Squarefree.Program.frameData small.regs ((s 330).reverse).reverse (s 334)=small := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,frameStacks]
  rw [heq] at ht
  have he := eval_call_from_state Squarefree.Program.frameEmitProgram frameRegisters frameStacks a
    frameRegisters_injective frameStacks_injective ht
  let out := Squarefree.Program.frameData rf [] (Encoding.frame (s 330).reverse++s 334)
  have hs : out.stacks=Function.update (Function.update small.stacks 0 []) 1
      (Encoding.frame (s 330).reverse++s 334) := by
    funext i; fin_cases i <;> simp [out,Squarefree.Program.frameData]
  have hh : (embedState frameRegisters frameStacks a out).stacks =
      Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334) := by
    change Function.extend frameStacks out.stacks s = _
    rw [hs,ProgramLinking.extend_update frameStacks_injective,
      ProgramLinking.extend_update frameStacks_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project frameRegisters frameStacks a frameRegisters_injective frameStacks_injective)
    change Function.extend frameStacks small.stacks s=s at hb
    rw [hb]
    rfl
  change Eval frameRow (4*(s 330).reverse.length+6) a
    (embedState frameRegisters frameStacks a out) at he
  have hout : embedState frameRegisters frameStacks a out=
      (⟨(embedState frameRegisters frameStacks a out).regs,
        Function.update (Function.update s 330 []) 334
          (Encoding.frame (s 330).reverse++s 334)⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hh
  rw [hout] at he
  exact ⟨4*(s 330).length+6,(embedState frameRegisters frameStacks a out).regs,
    le_rfl,by simpa [a] using he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem emitRow_run (s : Store) (h330 : s 330=[]) (h334 : s 334=[]) :
    ExecutesIn emitRow (13*(s 240).length+20) s
      (Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332)) := by
  let s1 := Function.update (Function.update s 240 []) 330 (s 240).reverse
  let s2 := Function.update (Function.update s1 330 []) 334 (Encoding.frame (s 240))
  let s3 := Function.update s2 334 (rowRecord (s 240))
  have h1 : ExecutesIn (transfer 240 330) (3*(s 240).length+3) s s1 := by
    simpa [s1,h330] using transfer_run 240 330 s (by decide)
  have h2 : ExecutesIn frameRow (4*(s 240).length+6) s1 s2 := by
    simpa [s1,s2,h334] using frameRow_run s1
  have h3 : ExecutesIn (push 334 true) 2 s2 s3 := by
    simpa [s3,s2,rowRecord] using push_run 334 true s2
  have h4 := transfer_run 334 332 s3 (by decide)
  have he : Function.update (Function.update s3 334 []) 332
      ((s3 334).reverse++s3 332)=
        Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h332 : i=332 <;>
      by_cases hh330 : i=330 <;> by_cases hh334 : i=334 <;>
      simp [s3,s2,s1,h240,h332,hh330,hh334,h330,h334]
  rw [he] at h4
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp [s3,s2,rowRecord]
  omega

theorem finishRows_run (s : Store) (h205 : s 205=[]) :
    ExecutesIn finishRows (3*(s 332).length+8) s
      (Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false])) := by
  have h1 := push_run 332 false s
  have h2 := transfer_run 332 205 (Function.update s 332 (false::s 332)) (by decide)
  have he : Function.update (Function.update (Function.update s 332 (false::s 332)) 332 [])
      205 ((Function.update s 332 (false::s 332) 332).reverse ++
      (Function.update s 332 (false::s 332) 205))=
        Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false]) := by
    simp [h205,List.reverse_cons]
  rw [he] at h2
  exact (h1.seq h2).mono (by simp; omega)

theorem rowBytes_succ (value : ℕ → List Bool) (j n : ℕ) :
    rowBytes value j (n+1)=rowRecord (value j)++rowBytes value (j+1) n := by
  simp [rowBytes,List.range'_succ]

theorem rowBytes_length (value : ℕ → List Bool) (W : ℕ)
    (hw : ∀ j, (value j).length=W) (j n : ℕ) :
    (rowBytes value j n).length=n*(2*W+2) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih => rw [rowBytes_succ,List.length_append,ih]; simp [rowRecord,hw]; ring

theorem rowBody_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (j : ℕ) (hj : j < N) (remaining acc : List Bool) :
    ExecutesIn (rowBody callback) (K+13*W+22) (rowState base j remaining acc)
      (rowState base (j+1) remaining ((rowRecord (value j)).reverse++acc)) := by
  let s := rowState base j remaining acc
  let s1 := Function.update s 240 (value j)
  let s2 := rowState base j remaining ((rowRecord (value j)).reverse++acc)
  have h1 : ExecutesIn callback K s s1 := spec j hj remaining acc
  have he2 : Function.update (Function.update s1 240 []) 332
      ((rowRecord (s1 240)).reverse++s1 332)=s2 := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;>
      by_cases h332 : i=332 <;> by_cases hh240 : i=240 <;>
      simp [s2,s1,s,rowState,h320,h331,h332,hh240,h240]
  have h2 : ExecutesIn emitRow (13*W+20) s1 s2 := by
    have h := emitRow_run s1 (by simp [s1,s,rowState,h330]) (by simp [s1,s,rowState,h334])
    rw [he2] at h
    simpa [s1,hw] using h
  have h3 := push_run 320 true s2
  have he3 : Function.update s2 320 (true::s2 320)=
      rowState base (j+1) remaining ((rowRecord (value j)).reverse++acc) := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [s2,rowState,h320,h331,h332,List.replicate_succ]
  rw [he3] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem row_popped (base : Store) (j : ℕ) (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped rowPorts (⟨regs,rowState base j remaining acc⟩ : Data)=
      (⟨readRegs regs 14 15 remaining.head?,rowState base j remaining.tail acc⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,rowPorts,rowState]
  · funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [UnaryForPrograms.popped,rowPorts,rowState,h320,h331,h332]

theorem row_visits (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) (regs : Fin 16 → Bool) :
    ∃ costs n rf, n ≤ remaining.length*(K+13*W+24)+2 ∧
      UnaryForPrograms.Visits rowPorts (rowBody callback) costs n
        (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+remaining.length) []
          ((rowBytes value j remaining.length).reverse++acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],2,readRegs regs 14 15 none,by simp,?_⟩
    simpa only [row_popped,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,rowBytes_zero,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := rowPorts) (body := rowBody callback)
        (⟨regs,rowState base j [] acc⟩ : Data) (by simp [rowState,rowPorts])
  | cons b remaining ih =>
    obtain ⟨nb,rb,hnb,hb⟩ := rowBody_run callback base value N K W spec hw h240 h330 h334
      j (by simp only [List.length_cons] at hj; omega) remaining acc (readRegs regs 14 15 (some b))
    obtain ⟨costs,nt,rt,hnt,ht⟩ := ih ((rowRecord (value j)).reverse++acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) rb
    refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := rowPorts) (body := rowBody callback)
        (d := (⟨regs,rowState base j (b::remaining) acc⟩ : Data))
        (by simp [rowState,rowPorts])
        (by simpa only [row_popped,List.head?_cons,List.tail_cons] using hb)
        (by simp [rowState,rowPorts,UnaryForPrograms.popped]) ht
      simpa only [List.length_cons,rowBytes_succ,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rowLoop_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) :
    ExecutesIn (rowLoop callback) (remaining.length*(K+13*W+24)+2)
      (rowState base j remaining acc)
      (rowState base (j+remaining.length) [] ((rowBytes value j remaining.length).reverse++acc)) := by
  intro regs
  obtain ⟨costs,n,rf,hn,he⟩ := row_visits callback base value N K W spec hw h240 h330 h334
    remaining acc j hj regs
  exact ⟨n,rf,hn,he.eval⟩

theorem rowsCommand_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) :
    ExecutesIn (rowsCommand callback) (N*(K+19*W+39)+18) base
      (Function.update base 205 (rowBytes value 0 N++[false])) := by
  let s1 := rowState base 0 (base 212) []
  let s2 := rowState base N [] (rowBytes value 0 N).reverse
  let s3 := Function.update s2 320 []
  have he1 : Function.update base 331 (base 212++base 331)=s1 := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;> by_cases hi332 : i=332 <;>
      simp [s1,rowState,hi320,hi331,hi332,h320,h331,h332]
  have h1 : ExecutesIn (copy 212 331) (7*N+5) base s1 := by
    have h := copy_run 212 331 base (by decide) (by decide) (by decide) h339
    rw [he1,hN] at h
    exact h
  have h2 : ExecutesIn (rowLoop callback) (N*(K+13*W+24)+2) s1 s2 := by
    have h := rowLoop_run callback base value N K W spec hw h240 h330 h334
      (base 212) [] 0 (by omega)
    simpa only [s1,s2,hN,Nat.zero_add,List.append_nil] using h
  have h3 : ExecutesIn (clear 320) (2*N+3) s2 s3 := by
    simpa [s2,rowState,s3] using clear_run 320 s2
  have he4 : Function.update (Function.update s3 332 []) 205
      ((s3 332).reverse++[false])=Function.update base 205 (rowBytes value 0 N++[false]) := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;>
      by_cases hi332 : i=332 <;> by_cases hi205 : i=205 <;>
      simp [s3,s2,rowState,hi320,hi331,hi332,hi205,h320,h331,h332]
  have h4 : ExecutesIn finishRows (3*(N*(2*W+2))+8) s3
      (Function.update base 205 (rowBytes value 0 N++[false])) := by
    have h := finishRows_run s3 (by simp [s3,s2,rowState,h205])
    rw [he4] at h
    simpa [s3,s2,rowState,rowBytes_length value W hw] using h
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by ring_nf; omega)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

theorem records_encoding (encode : Witness → List Bool) (ws : List Witness) :
    records encode ws++[false]=Encoding.encodeList encode ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simpa [records,rowRecord,Encoding.encodeList,List.append_assoc] using
        (congrArg (fun b => rowRecord (encode w)++b) ih)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Absent factor incidences have zero source polynomials. This branch copies
the initialized zero array once per ambient coordinate and emits every row. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem zeroRow_spec (base : Store) (bits : List Bool) (N : ℕ)
    (hz : base 192=bits) (h240 : base 240=[]) (h339 : base 339=[]) :
    RowSpec zeroRow base (fun _ => bits) N (7*bits.length+5) := by
  intro j _ remaining acc
  have h := copy_run 192 240 (rowState base j remaining acc)
    (by decide) (by decide) (by decide) (by simpa [rowState] using h339)
  simpa [zeroRow,rowState,hz,h240] using h

theorem constantRows_encoding (bits : List Bool) (j N : ℕ) :
    rowBytes (fun _ => bits) j N++[false]=Encoding.encodeList id (List.replicate N bits) := by
  rw [←records_encoding]
  have h : (List.range' j N).map (fun _ => bits)=List.replicate N bits := by simp
  rw [←h]
  simp [records,rowBytes]
  induction N with
  | zero => rfl
  | succ N ih => simp [List.replicate_succ,ih]

theorem zeroRows_run_oai (base : Store) (bits : List Bool) (N : ℕ)
    (hz : base 192=bits) (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) :
    ExecutesIn zeroRows (N*(26*bits.length+44)+18) base
      (Function.update base 205 (Encoding.encodeList id (List.replicate N bits))) := by
  have hr := rowsCommand_run zeroRow base (fun _ => bits) N (7*bits.length+5) bits.length
    (zeroRow_spec base bits N hz h240 h339) (fun _ => rfl) hN
    h240 h330 h334 h320 h331 h332 h205 h339
  have hc : 7*bits.length+5+19*bits.length+39=26*bits.length+44 := by omega
  simpa [zeroRows,constantRows_encoding,hc] using hr

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run_oai
