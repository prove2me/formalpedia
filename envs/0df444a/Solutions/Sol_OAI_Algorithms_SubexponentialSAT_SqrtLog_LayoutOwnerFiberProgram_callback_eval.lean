-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:26:54.380352+00:00
-- url     : https://prove2.me/submissions/d986db09-5e39-42ad-9fee-d83214806041

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

open BitProgram StructuredCalls SubexpScanPrimitives

namespace Internal

theorem comparePorts_injective : Function.Injective comparePorts := by decide

theorem compare_eval (regs : Fin 5 → Bool)
    (query master source left right tmp count : List Bool) :
    ∃ n ≤ 9 * (left.length + 1), ∃ regs' left' right',
      Eval compare n
        (state regs query master source left right tmp count)
        (state regs' query master source left' right' tmp count) ∧
      regs' 4 = decide (left = right) ∧
      left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded regs left right
  let d := state regs query master source left right tmp count
  let a : State 5 2 := ⟨regs, ExecClauseCost.bitStacks left right⟩
  let b : State 5 2 := ⟨c.regs, c.stacks⟩
  have ha : embedState id comparePorts d a = d := by
    apply embedState_eq id comparePorts Function.injective_id comparePorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState id comparePorts d b =
      state c.regs query master source (c.stacks 0) (c.stacks 1) tmp count := by
    apply embedState_eq id comparePorts Function.injective_id comparePorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i hi
      fin_cases i <;> first | exact False.elim (hi ⟨0,rfl⟩)
                            | exact False.elim (hi ⟨1,rfl⟩) | rfl
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  have he := eval_call_lifted ExecClauseCost.bitEqualityProgram id comparePorts d
    Function.injective_id comparePorts_injective ht'
  refine ⟨n,hn,c.regs,c.stacks 0,c.stacks 1,?_,hout,hleft,hright⟩
  simpa only [ha,hb,compare] using he

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

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

theorem forward_eval (regs : Fin 5 → Bool)
    (q m s bits w t i a c o : List Bool) :
    Eval forward (3*bits.length+3)
      (data regs q m s bits.reverse [] w t i a c o)
      (data (status regs false false) q m s [] bits w t i a c o) := by
  have h := transfer_eval (data regs q m s bits.reverse [] w t i a c o)
    3 4 0 1 (by decide) (by decide)
  convert h using 1
  · rfl
  · simp [data]
  · apply state_ext
    · simp [afterTransfer,data]
    · funext j; fin_cases j <;> simp [afterTransfer,data,StackRoutines.transferStacks]

theorem read_state (regs : Fin 5 → Bool)
    (q m s payload decoded w t i a c o bits tail : List Bool) (v p : Bool) :
    RecordPrograms.state readPorts (data regs q m s payload decoded w t i a c o)
      v p (regs 4) tail bits = data (status regs v p) q m s bits tail w t i a c o := by
  apply state_ext
  · funext j; fin_cases j <;> simp [RecordPrograms.state,readPorts,data,status]
  · funext j; fin_cases j <;> simp [RecordPrograms.state,readPorts,data]

theorem readFrame_eval (regs : Fin 5 → Bool)
    (q m s bits tail w t i a c o : List Bool) :
    Eval readFrame (6*bits.length+4)
      (data regs q m s [] (Encoding.frame bits++tail) w t i a c o)
      (data (status regs false true) q m s bits.reverse tail w t i a c o) := by
  have h := RecordPrograms.reader_eval readPorts
    (data regs q m s [] (Encoding.frame bits++tail) w t i a c o)
    bits tail [] (regs 0) (regs 1) (regs 4)
  rw [read_state,read_state] at h
  have he : status regs (regs 0) (regs 1)=regs := by
    funext j; fin_cases j <;> simp [status]
  simpa [readFrame,he] using h

theorem popDecoded_eval (regs : Fin 5 → Bool) (b : Bool)
    (q m s payload tail w t i a c o : List Bool) :
    Eval popDecoded 1 (data regs q m s payload (b::tail) w t i a c o)
      (data (status regs b true) q m s payload tail w t i a c o) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (4 : Fin 11) (0 : Fin 5) 1)
    (data regs q m s payload (b::tail) w t i a c o))
  convert h using 1
  · rfl
  · apply state_ext
    · funext j; fin_cases j <;> simp [data,status,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr,readRegs]
    · funext j; fin_cases j <;> simp [data,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

theorem clear_eval (src : Fin 11) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  have h := ListRegisterProgram.clear_run src (0 : Fin 5) 1 d.regs d.stacks
  apply Eval.call
  simpa [clear,cleared,StructuredProgram.State.withPC,StackRoutines.clearStacks] using h

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem compareSlots_injective : Function.Injective compareSlots := by decide

theorem compare_eval (regs : Fin 5 → Bool)
    (q m s left decoded right tmp i a c o : List Bool) :
    ∃ n ≤ 9*(left.length+1)+1, ∃ rr left' right',
      Eval compare n (data regs q m s left decoded right tmp i a c o)
        (data rr q m s left' decoded right' tmp i a c o) ∧
      rr 4=decide (left=right) ∧ left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  obtain ⟨n,hn,rr,l,r,he,hf,hl,hr⟩ :=
    SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare_eval regs q m s left right tmp i
  let d := data regs q m s left decoded right tmp i a c o
  have hin : projectState id compareSlots d=
      SubexponentialSAT.SubexpNodeIndexProgram.Internal.state regs q m s left right tmp i := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  rw [← hin] at he
  have h := eval_liftCommand_from_state SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare
    3 4 id compareSlots d Function.injective_id compareSlots_injective he
  have hout : embedState id compareSlots d
      (SubexponentialSAT.SubexpNodeIndexProgram.Internal.state rr q m s l r tmp i)=
        data rr q m s l decoded r tmp i a c o := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id compareSlots_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> simp_all [d,data,compareSlots,Fin.exists_fin_succ]
  rw [hout] at h
  exact ⟨n+1,by omega,rr,l,r,h,hf,hl,hr⟩

theorem copyQuery_eval (regs : Fin 5 → Bool)
    (q m s owner i a c o : List Bool) :
    Eval copyQuery (7*q.length+5)
      (data regs q m s owner [] [] [] i a c o)
      (data (status regs false false) q m s owner [] q [] i a c o) := by
  have h := copy_eval (data regs q m s owner [] [] [] i a c o)
    0 5 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · rfl
  · simp [data]
  · apply state_ext
    · simp [afterCopy,data]
    · funext j; fin_cases j <;> simp [afterCopy,data,StackRoutines.copyStacks]

/-- Both originals are preserved; consumed equality operands and residuals
are cleared with their actual lengths charged. -/
theorem compareOwner_eval (regs : Fin 5 → Bool)
    (q m s owner i a c o : List Bool) :
    ∃ n ≤ 11*owner.length+9*q.length+21, ∃ rr,
      Eval compareOwner n (data regs q m s owner [] [] [] i a c o)
        (data rr q m s [] [] [] [] i a c o) ∧ rr 4=decide (owner=q) := by
  have h1 := copyQuery_eval regs q m s owner i a c o
  obtain ⟨n,hn,rr,l,r,h2,hf,hl,hr⟩ :=
    compare_eval (status regs false false) q m s owner [] q [] i a c o
  have h3 := clear_eval 3 (data rr q m s l [] r [] i a c o)
  have he3 : cleared (data rr q m s l [] r [] i a c o) 3=
      data (status rr false false) q m s [] [] r [] i a c o := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [he3] at h3
  have h4 := clear_eval 5 (data (status rr false false) q m s [] [] r [] i a c o)
  have he4 : cleared (data (status rr false false) q m s [] [] r [] i a c o) 5=
      data (status rr false false) q m s [] [] [] [] i a c o := by
    apply state_ext
    · simp [cleared,data]
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [he4] at h4
  refine ⟨(7*q.length+5)+(n+((2*l.length+3)+(2*r.length+3))),by omega,
    status rr false false,?_,?_⟩
  · exact h1.seq (h2.seq (h3.seq h4))
  · simpa [status] using hf

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem normalize_eval (d : Data) : Eval normalize 3 d ⟨reset d.regs,d.stacks⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 5) false) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 5) true)
    ((StructuredProgram.Atom.set (0 : Fin 5) false).eval d))
  have h3 := Eval.base (StructuredProgram.Eval.atom (.set (4 : Fin 5) false)
    ((StructuredProgram.Atom.set (1 : Fin 5) true).eval
      ((StructuredProgram.Atom.set (0 : Fin 5) false).eval d)))
  simpa [normalize,reset,status,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h1.seq (h2.seq h3)

theorem emitMatch_eval (regs : Fin 5 → Bool) (q m s acc out : List Bool) (j count : ℕ) :
    Eval emitMatch (7*j+9)
      (data regs q m s [] [] [] [] (unary j) acc (unary count) out)
      (data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out) := by
  let a := data regs q m s [] [] [] [] (unary j) acc (unary count) out
  let b := data (status regs false false) q m s [] [] [] [] (unary j)
    (unary j++acc) (unary count) out
  have h1 := copy_eval a 7 8 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hb : afterCopy a 7 8 0 1=b := by
    apply state_ext
    · simp [a,b,afterCopy,data]
    · funext k; fin_cases k <;> simp [a,b,afterCopy,data,StackRoutines.copyStacks]
  rw [hb] at h1
  have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (8 : Fin 11) (0 : Fin 5) false b
  have h3 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (9 : Fin 11) (0 : Fin 5) true (pushed 8 0 false b)
  change Eval (push 9 0 true) 2 (pushed 8 0 false b)
    (pushed 9 0 true (pushed 8 0 false b)) at h3
  have he : pushed 9 0 true (pushed 8 0 false b)=
      data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out := by
    apply state_ext
    · funext k; fin_cases k <;> simp [b,status,data]
    · funext k; fin_cases k <;>
        simp [b,data,Encoding.encodeNat,
          List.reverse_append,List.replicate_succ]
  rw [he] at h3
  have hh := h1.seq (h2.seq h3)
  simpa [emitMatch,a,data,Nat.add_assoc] using hh

theorem finish_eval (regs : Fin 5 → Bool) (q m s acc out : List Bool)
    (j count : ℕ) (matched : Bool) (hf : regs 4=matched) :
    ∃ n ≤ 7*j+15,
      Eval finish n (data regs q m s [] [] [] [] (unary j) acc (unary count) out)
        (data (reset regs) q m s [] [] [] [] (unary (j+1))
          (if matched then (Encoding.encodeNat j).reverse++acc else acc)
          (unary (count+(if matched then 1 else 0))) out) := by
  cases matched with
  | false =>
      let a := data regs q m s [] [] [] [] (unary j) acc (unary count) out
      have h1 : Eval (.ite 4 emitMatch (.base .skip)) 1 a a :=
        Eval.ite_false hf (Eval.base (StructuredProgram.Eval.skip a))
      have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (7 : Fin 11) (0 : Fin 5) true a
      have h3 := normalize_eval (pushed 7 0 true a)
      refine ⟨6,by omega,?_⟩
      have he : (⟨reset (pushed 7 0 true a).regs,(pushed 7 0 true a).stacks⟩ : Data)=
          data (reset regs) q m s [] [] [] [] (unary (j+1)) acc (unary count) out := by
        apply state_ext
        · funext k; fin_cases k <;> simp [a,reset,status,data]
        · funext k; fin_cases k <;> simp [a,data,List.replicate_succ]
      rw [he] at h3
      simpa only [finish,Bool.false_eq_true,ite_false,Nat.add_zero] using h1.seq (h2.seq h3)
  | true =>
      let b := data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out
      have h1 := Eval.ite_true (no := (.base .skip)) hf (emitMatch_eval regs q m s acc out j count)
      have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (7 : Fin 11) (0 : Fin 5) true b
      have h3 := normalize_eval (pushed 7 0 true b)
      refine ⟨7*j+15,le_rfl,?_⟩
      have he : (⟨reset (pushed 7 0 true b).regs,(pushed 7 0 true b).stacks⟩ : Data)=
          data (reset regs) q m s [] [] [] [] (unary (j+1))
            ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out := by
        apply state_ext
        · funext k; fin_cases k <;> simp [b,reset,status,data]
        · funext k; fin_cases k <;> simp [b,data,List.replicate_succ]
      rw [he] at h3
      have hh := h1.seq (h2.seq h3)
      simpa [finish,b,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- The second address is consumed and charged; only the original owner word
is exposed to the comparison stage. The outer scan tail is preserved. -/
theorem parseOwner_eval (regs : Fin 5 → Bool) (v f : ℕ)
    (q m s i a c o : List Bool) :
    Eval parseOwner (36*v+34*f+102)
      (data regs q m s (pairPayload v f).reverse [] [] [] i a c o)
      (data (status regs false false) q m s (unary v) [] [] [] i a c o) := by
  have h1 := forward_eval regs q m s (pairPayload v f) [] [] i a c o
  have h2 := readFrame_eval (status regs false false) q m s (pairBytes v f) [] [] [] i a c o
  have h3 := forward_eval (status regs false true) q m s (pairBytes v f) [] [] i a c o
  have h4 := popDecoded_eval (status regs false false) true q m s []
    (Encoding.frame (unary v)++pairTail f) [] [] i a c o
  have h5 := readFrame_eval (status regs true true) q m s (unary v) (pairTail f) [] [] i a c o
  have h6 := clear_eval 4 (data (status regs false true) q m s (unary v) (pairTail f) [] [] i a c o)
  have h6e : cleared (data (status regs false true) q m s (unary v) (pairTail f)
      [] [] i a c o) 4 = data (status regs false false) q m s (unary v) [] [] [] i a c o := by
    apply state_ext
    · simp [cleared,data]
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [h6e] at h6
  have hvrev : (unary v).reverse=unary v := by simp
  simp only [status_status,List.append_nil,hvrev] at h2 h3 h4 h5
  have hp : pairBytes v f=true::(Encoding.frame (unary v)++pairTail f) := rfl
  rw [hp] at h3
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert hh using 1 <;>
    simp [parseOwner,pairPayload,pairBytes,pairTail,ProgramEncoding.encodeRecords,
      Encoding.encodeList,Encoding.length_frame,data] ; omega

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

theorem callback_eval_oai (regs : Fin 5 → Bool) (query index count : ℕ)
    (v f : ℕ) (master tail acc out : List Bool) :
    ∃ n ≤ callbackCost query index (v,f), ∃ rr,
      Eval callback n
        (data regs (unary query) master tail (pairPayload v f).reverse [] [] []
          (unary index) acc (unary count) out)
        (data (reset rr) (unary query) master tail [] [] [] [] (unary (index+1))
          (if v=query then (Encoding.encodeNat index).reverse++acc else acc)
          (unary (count+(if v=query then 1 else 0))) out) := by
  have h1 := parseOwner_eval regs v f (unary query) master tail (unary index) acc (unary count) out
  obtain ⟨n2,hn2,r2,h2,hflag⟩ := compareOwner_eval (status regs false false)
    (unary query) master tail (unary v) (unary index) acc (unary count) out
  have hf : r2 4=decide (v=query) := by simpa using hflag
  obtain ⟨n3,hn3,h3⟩ := finish_eval r2 (unary query) master tail acc out index count
    (decide (v=query)) hf
  refine ⟨(36*v+34*f+102)+(n2+n3),?_,r2,?_⟩
  · simp only [List.length_replicate] at hn2
    unfold callbackCost
    omega
  · simpa only [callback,decide_eq_true_eq] using h1.seq (h2.seq h3)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval_oai
