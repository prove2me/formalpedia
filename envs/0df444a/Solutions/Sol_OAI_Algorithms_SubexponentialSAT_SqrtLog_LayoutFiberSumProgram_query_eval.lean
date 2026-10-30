-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:50:04.639628+00:00
-- url     : https://prove2.me/submissions/d0114c10-7ccc-4822-b0d4-a59913735728

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram_callback_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem clear_eval (src : Fin 11) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  have h := ListRegisterProgram.clear_run src (0 : Fin 5) 1 d.regs d.stacks
  apply Eval.call
  simpa [clear,cleared,StructuredProgram.State.withPC,StackRoutines.clearStacks] using h

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem outerRead_eval (regs : Fin 5 → Bool)
    (q m bits tail i a c o : List Bool) :
    Eval outerRead (6*bits.length+4)
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      (data (status regs false true) q m tail bits.reverse [] [] [] i a c o) := by
  have h := RecordPrograms.reader_eval outerPorts
    (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
    bits tail [] (regs 0) (regs 1) (regs 4)
  have hin : RecordPrograms.state outerPorts
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      (regs 0) (regs 1) (regs 4) (Encoding.frame bits++tail) []=
      data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o := by
    apply RecordPrograms.state_eq_self <;> rfl
  have hout : RecordPrograms.state outerPorts
      (data regs q m (Encoding.frame bits++tail) [] [] [] [] i a c o)
      false true (regs 4) tail (bits.reverse++[])=
      data (status regs false true) q m tail bits.reverse [] [] [] i a c o := by
    apply state_ext
    · funext j; fin_cases j <;> simp [RecordPrograms.state,outerPorts,data,status]
    · funext j; fin_cases j <;> simp [RecordPrograms.state,outerPorts,data]
  rw [hin,hout] at h
  exact h

theorem popScan_eval (regs : Fin 5 → Bool) (b : Bool)
    (q m tail i a c o : List Bool) :
    Eval popScan 1 (data regs q m (b::tail) [] [] [] [] i a c o)
      (data (status regs b true) q m tail [] [] [] [] i a c o) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 11) (0 : Fin 5) 1)
    (data regs q m (b::tail) [] [] [] [] i a c o))
  convert h using 1
  · rfl
  · apply state_ext
    · funext j; fin_cases j <;> simp [data,status,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext j; fin_cases j <;> simp [data,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stream_head (ps : List (ℕ × ℕ)) : stream ps=(!ps.isEmpty)::(stream ps).tail := by
  cases ps <;> rfl

/-- Every plan record is physically read. The index advances even when the
owner comparison fails, so returned numbers are original incidence positions. -/
theorem loop_eval (ps : List (ℕ × ℕ)) (query index count : ℕ)
    (regs : Fin 5 → Bool) (master acc out : List Bool) :
    ∃ n ≤ scanCost query index ps, ∃ rf,
      Eval loop n
        (data (status regs (!ps.isEmpty) true) (unary query) master (stream ps).tail
          [] [] [] [] (unary index) acc (unary count) out)
        (data rf (unary query) master [] [] [] [] [] (unary (index+ps.length))
          ((encodeIndices (fiberIndices query index ps)).reverse++acc)
          (unary (count+(fiberIndices query index ps).length)) out) := by
  induction ps generalizing index count regs acc with
  | nil =>
      refine ⟨1,by simp [scanCost],status regs false true,?_⟩
      simpa [loop,stream,Encoding.encodeList,fiberIndices,encodeIndices] using
        (Eval.while_false (test := (0 : Fin 5)) (body := body)
          (a := data (status regs false true) (unary query) master [] [] [] [] []
            (unary index) acc (unary count) out) (by simp [data,status]))
  | cons p ps ih =>
      rcases p with ⟨v,f⟩
      have h1 := outerRead_eval (status regs true true) (unary query) master
        (pairPayload v f) (stream ps) (unary index) acc (unary count) out
      simp only [status_status] at h1
      obtain ⟨n2,hn2,r2,h2⟩ := callback_eval (status regs false true) query index count
        v f master (stream ps) acc out
      let acc' := if v=query then (Encoding.encodeNat index).reverse++acc else acc
      let count' := count+(if v=query then 1 else 0)
      have h3 := popScan_eval (reset r2) (!ps.isEmpty) (unary query) master
        (stream ps).tail (unary (index+1)) acc' (unary count') out
      rw [← stream_head ps] at h3
      obtain ⟨nt,hnt,rf,ht⟩ := ih (index+1) count' (reset r2) acc'
      have hb := h1.seq (h2.seq h3)
      have hh := Eval.while_true (test := (0 : Fin 5)) (by simp [data,status]) hb ht
      refine ⟨(6*(pairPayload v f).length+4)+(n2+1)+nt+1,?_,rf,?_⟩
      · simp only [scanCost]
        omega
      · convert hh using 1 <;>
          by_cases hv : v=query <;>
          simp [loop,body,stream,Encoding.encodeList,fiberIndices,encodeIndices,hv,
            acc',count',List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem scan_eval (ps : List (ℕ × ℕ)) (query index count : ℕ)
    (regs : Fin 5 → Bool) (master acc out : List Bool) :
    ∃ n ≤ scanCost query index ps+1, ∃ rf,
      Eval scan n
        (data regs (unary query) master (stream ps) [] [] [] []
          (unary index) acc (unary count) out)
        (data rf (unary query) master [] [] [] [] [] (unary (index+ps.length))
          ((encodeIndices (fiberIndices query index ps)).reverse++acc)
          (unary (count+(fiberIndices query index ps).length)) out) := by
  have hp := popScan_eval regs (!ps.isEmpty) (unary query) master (stream ps).tail
    (unary index) acc (unary count) out
  rw [← stream_head ps] at hp
  obtain ⟨n,hn,rf,he⟩ := loop_eval ps query index count regs master acc out
  exact ⟨1+n,by omega,rf,hp.seq he⟩

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem command_eval (query : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 5 → Bool) :
    ∃ n < budget query ps, ∃ rf,
      Eval command n (data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] [])
        (data rf (unary query) (stream ps) [] [] [] [] [] [] []
          (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))) := by
  let a := data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []
  have h1 := copy_eval a 1 2 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have he1 : afterCopy a 1 2 0 1=
      data (status regs false false) (unary query) (stream ps) (stream ps) [] [] [] [] [] [] [] [] := by
    apply state_ext
    · simp [afterCopy,a,data]
    · funext i; fin_cases i <;> simp [afterCopy,a,data,StackRoutines.copyStacks]
  rw [he1] at h1
  obtain ⟨n,hn,rr,h2⟩ := scan_eval ps query 0 0 (status regs false false) (stream ps) [] []
  simp only [Nat.zero_add,List.replicate_zero,List.append_nil] at h2
  let bits := encodeIndices (fiberIndices query 0 ps)
  have h3 := clear_eval 7 (data rr (unary query) (stream ps) [] [] [] [] []
    (unary ps.length) bits.reverse (unary (fiberIndices query 0 ps).length) [])
  have he3 : cleared (data rr (unary query) (stream ps) [] [] [] [] []
      (unary ps.length) bits.reverse (unary (fiberIndices query 0 ps).length) []) 7=
      data (status rr false false) (unary query) (stream ps) [] [] [] [] [] []
        bits.reverse (unary (fiberIndices query 0 ps).length) [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [cleared,data]
  rw [he3] at h3
  let b := data (status rr false false) (unary query) (stream ps) [] [] [] [] [] []
    bits.reverse (unary (fiberIndices query 0 ps).length) []
  have h4 := transfer_eval b 8 10 0 1 (by decide) (by decide)
  have he4 : afterTransfer b 8 10 0 1=
      data (status rr false false) (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) bits := by
    apply state_ext
    · simp [afterTransfer,b,data]
    · funext i; fin_cases i <;> simp [afterTransfer,b,data,StackRoutines.transferStacks]
  rw [he4] at h4
  have hh := h1.seq (h2.seq (h3.seq h4))
  refine ⟨7*(stream ps).length+5+(n+(2*ps.length+3+(3*bits.length+3))),?_,
    status rr false false,?_⟩
  · unfold budget
    dsimp only [bits]
    omega
  · simpa [command,copySource,restore,a,b,data,bits] using hh

/-- Source and original query are preserved. Output10 is the raw concatenation
of canonical incidence-index fields, with no list or frame oracle supplied. -/
theorem program_runs (query : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program (budget query ps)
      ((data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []).withPC (some program.entry))
      ((data rf (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval query ps regs
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 10⟩

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem ownerRegisters_injective : Function.Injective ownerRegisters := Fin.castAdd_injective _ _
theorem ownerStacks_injective : Function.Injective ownerStacks := by decide

theorem findOwner_eval (a : Data) (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : a.stacks 216=unary query)
    (hs : a.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (he : ∀ i : Fin 11, 2 ≤ i.val → a.stacks (ownerStacks i)=[]) :
    ∃ n ≤ LayoutOwnerFiberProgram.budget query ps, ∃ rf,
      Eval findOwner n a
        (ownerResult a rf (LayoutOwnerFiberProgram.fiberIndices query 0 ps)) := by
  obtain ⟨rf,n,hn,ht⟩ := LayoutOwnerFiberProgram.program_runs query ps (a.regs ∘ ownerRegisters)
  have hi : projectState ownerRegisters ownerStacks a=
      LayoutOwnerFiberProgram.data (a.regs ∘ ownerRegisters) (unary query)
        (LayoutOwnerFiberProgram.stream ps) [] [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hh : 2 ≤ i.val
      · have hz := he i hh
        fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
      · fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
  change Trace LayoutOwnerFiberProgram.program n
    ((LayoutOwnerFiberProgram.data (a.regs ∘ ownerRegisters) (unary query)
      (LayoutOwnerFiberProgram.stream ps) [] [] [] [] [] [] [] [] []).withPC
        (some LayoutOwnerFiberProgram.program.entry)) _ at ht
  rw [←hi] at ht
  have hc := eval_call_from_state LayoutOwnerFiberProgram.program ownerRegisters ownerStacks a
    ownerRegisters_injective ownerStacks_injective ht
  let out := LayoutOwnerFiberProgram.data rf (unary query) (LayoutOwnerFiberProgram.stream ps)
    [] [] [] [] [] [] [] (unary (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length)
      (encodeIndices (LayoutOwnerFiberProgram.fiberIndices query 0 ps))
  let rr := (embedState ownerRegisters ownerStacks a out).regs
  have ho : embedState ownerRegisters ownerStacks a out=
      ownerResult a rr (LayoutOwnerFiberProgram.fiberIndices query 0 ps) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hp : ∃ j, ownerStacks j=i
      · obtain ⟨j,rfl⟩ := hp
        have hh := embedState_stack ownerRegisters ownerStacks a out ownerStacks_injective j
        exact hh.trans (by
          by_cases hj : 2 ≤ j.val
          · have hz := he j hj
            fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks]
          · fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks])
      · have hh := embedState_stack_frame ownerRegisters ownerStacks a out i hp
        have h214 : i≠214 := fun h => hp ⟨10,h.symm⟩
        have h215 : i≠215 := fun h => hp ⟨9,h.symm⟩
        exact hh.trans (by simp [h214,h215])
  change Eval findOwner n a (embedState ownerRegisters ownerStacks a out) at hc
  rw [ho] at hc
  exact ⟨n,hn,rr,hc⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem query_eval_oai (base : Data) (hb : Ready base) (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps) (regs : Fin 16 → Bool) :
    ∃ n ≤ LayoutOwnerFiberProgram.budget query ps+2*(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length+3,
      ∃ rf, Eval (.seq findOwner clearCount) n
        (data (parked base query) regs [] [] ([],[]) ([],[]))
        (data (parked base query) rf
          (encodeIndices (LayoutOwnerFiberProgram.fiberIndices query 0 ps)) [] ([],[]) ([],[])) := by
  let a := data (parked base query) regs [] [] ([],[]) ([],[])
  let is := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  obtain ⟨n,hn,rr,hr⟩ := findOwner_eval a query ps
    (by simp [a,data,bank,parked]) (by simpa [a,data,bank,parked] using hs)
    (by
      intro i hi
      fin_cases i <;> simp_all [ownerStacks,a,data,bank,parked]
      all_goals exact hb.2 _ (by decide) (by decide))
  have hc := SubexponentialSAT.Subexp.TupleProgram.clear_eval (215 : Fin 256) (0 : Fin 16) 1
    (ownerResult a rr is)
  have he : (⟨readRegs rr 0 1 none,
      StackRoutines.clearStacks 215 (ownerResult a rr is).stacks⟩ : Data)=
      data (parked base query) (readRegs rr 0 1 none) (encodeIndices is) [] ([],[]) ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h215 : i=215
      · subst i
        simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked,
          hb.2 215 (by decide) (by decide)]
      by_cases h214 : i=214
      · subst i; simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked]
      simp [StackRoutines.clearStacks,ownerResult,a,data,bank,parked,h215,h214]
  change Eval clearCount _ _ (⟨readRegs rr 0 1 none,
      StackRoutines.clearStacks 215 (ownerResult a rr is).stacks⟩ : Data) at hc
  rw [he] at hc
  have hh := hr.seq hc
  refine ⟨_,?_,readRegs rr 0 1 none,hh⟩
  simp only [ownerResult,Function.update_of_ne (show (215 : Fin 256)≠214 by decide),
    Function.update_same,unary,List.length_replicate]
  dsimp only [is]
  omega

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval_oai
