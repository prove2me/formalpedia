-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:31:33.457815+00:00
-- url     : https://prove2.me/submissions/f402ce7d-0fa3-45ea-9c9e-29db56e77078

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
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

theorem outer_state (regs : Fin 5 → Bool)
    (query master source payload work tmp count : List Bool)
    (v pr f : Bool) (source' payload' : List Bool) :
    RecordPrograms.state ports (state regs query master source payload work tmp count)
      v pr f source' payload' =
      state (normalized regs v pr f) query master source' payload' work tmp count := by
  apply state_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, state, store]

theorem clear_eval (d : Data) (src : Fin 7) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clear, cleared, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh

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

theorem bump_eval (d : Data) : Eval bump 2 d
    ⟨Function.update d.regs 0 true, Function.update d.stacks 6 (true :: d.stacks 6)⟩ := by
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 5) true) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.push (6 : Fin 7) 0)
    ((StructuredProgram.Atom.set 0 true).eval d))
  simpa [bump, RecordPrograms.atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h₁.seq h₂

theorem normalize_eval (d : Data) : Eval normalize 2 d
    ⟨Function.update (Function.update d.regs 0 false) 1 true, d.stacks⟩ := by
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 5) false) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 5) true)
    ((StructuredProgram.Atom.set 0 false).eval d))
  simpa [normalize, RecordPrograms.atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h₁.seq h₂

theorem finish_eval (regs : Fin 5 → Bool)
    (query master source count : List Bool) (matched : Bool) (hflag : regs 4 = matched) :
    ∃ n ≤ 5, ∃ regs',
      Eval finish n (state regs query master source [] [] [] count)
        (state (normalized regs' false true matched) query master source [] [] []
          (if matched then count else true :: count)) := by
  let d := state regs query master source [] [] [] count
  cases matched with
  | false =>
      let e : Data := ⟨Function.update d.regs 0 true,
        Function.update d.stacks 6 (true :: d.stacks 6)⟩
      have hb : Eval (.ite 4 (.base .skip) bump) 3 d e :=
        Eval.ite_false hflag (bump_eval d)
      have hn := normalize_eval e
      have he : (⟨Function.update (Function.update e.regs 0 false) 1 true,e.stacks⟩ : Data) =
          state (normalized regs false true false) query master source [] [] []
            (true :: count) := by
        apply state_ext
        · funext i; fin_cases i <;> simp [e,d,state,normalized,hflag]
        · funext i; fin_cases i <;> simp [e,d,state,store]
      rw [he] at hn
      exact ⟨5,le_rfl,regs,hb.seq hn⟩
  | true =>
      have hb : Eval (.ite 4 (.base .skip) bump) 1 d d :=
        Eval.ite_true hflag (Eval.base (StructuredProgram.Eval.skip d))
      have hn := normalize_eval d
      have he : (⟨Function.update (Function.update d.regs 0 false) 1 true,d.stacks⟩ : Data) =
          state (normalized regs false true true) query master source [] [] [] count := by
        apply state_ext
        · funext i; fin_cases i <;> simp [d,state,normalized,hflag]
        · rfl
      rw [he] at hn
      exact ⟨3,by decide,regs,hb.seq hn⟩

theorem callback_eval (regs : Fin 5 → Bool)
    (query master source key count : List Bool) :
    ∃ n ≤ callbackCost query key, ∃ regs',
      Eval callback n (state regs query master source key.reverse [] [] count)
        (state (normalized regs' false true (decide (key = query)))
          query master source [] [] [] (if key = query then count else true :: count)) := by
  let a := state regs query master source key.reverse [] [] count
  let r₁ := readRegs regs 0 1 none
  let r₂ := readRegs r₁ 0 1 none
  have hrev := reverse_eval a 3 4 5 0 1 (by decide) (by decide) (by decide)
    (by decide) rfl rfl
  have hrevEnd : afterReverse a 3 0 1 = state r₁ query master source key [] [] count := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [a,afterReverse,StackRoutines.reverseStacks,state,store]
  have hrevLen : (a.stacks 3).length = key.length := by simp [a,state,store]
  rw [hrevEnd,hrevLen] at hrev
  let b := state r₁ query master source key [] [] count
  have hc := copy_eval b 0 4 5 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hcEnd : afterCopy b 0 4 0 1 = state r₂ query master source key query [] count := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [b,afterCopy,StackRoutines.copyStacks,state,store]
  have hcLen : (b.stacks 0).length = query.length := rfl
  rw [hcEnd,hcLen] at hc
  obtain ⟨nc,hnc,rr,left,right,hm,hflag,hl,hr⟩ :=
    compare_eval r₂ query master source key query [] count
  let c := state rr query master source left right [] count
  let r₃ := readRegs rr 0 1 none
  have hcl := clear_eval c 3
  have hclEnd : cleared c 3 = state r₃ query master source [] right [] count := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [c,cleared,state,store]
  have hclLen : (c.stacks 3).length = left.length := rfl
  rw [hclEnd,hclLen] at hcl
  let d := state r₃ query master source [] right [] count
  let r₄ := readRegs r₃ 0 1 none
  have hcr := clear_eval d 4
  have hcrEnd : cleared d 4 = state r₄ query master source [] [] [] count := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,cleared,state,store]
  have hcrLen : (d.stacks 4).length = right.length := rfl
  rw [hcrEnd,hcrLen] at hcr
  have hflag' : r₄ 4 = decide (key = query) := by
    first | (simpa [r₄,r₃,readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hflag) | (simpa [r₄,r₃,readRegs] using hflag)
  obtain ⟨nf,hnf,rf,hf⟩ := finish_eval r₄ query master source count _ hflag'
  refine ⟨(9*key.length+7)+((7*query.length+5)+(nc+((2*left.length+3)+
    ((2*right.length+3)+nf)))),?_,rf,?_⟩
  · unfold callbackCost
    omega
  · simpa only [callback,copy,decide_eq_true_eq] using
      hrev.seq (hc.seq (hm.seq (hcl.seq (hcr.seq hf))))

theorem callback_contract (query master : List Bool) :
    RecordPrograms.CallbackContractWith ports callback (fun key => decide (key = query))
      (callbackCost query) (invariant query master) (effect query) := by
  intro key tail base hbase
  obtain ⟨regs,count,rfl⟩ := hbase
  obtain ⟨n,hn,rr,he⟩ := callback_eval (normalized regs false true false)
    query master tail key count
  let next := state (normalized rr false true (decide (key = query)))
    query master [] [] [] [] (if key = query then count else true :: count)
  refine ⟨n,next,hn,⟨_,_,rfl⟩,?_,?_⟩
  · rfl
  · simpa only [outer_state,normalized_normalized,next] using he

theorem visits_count (query : List Bool) {nodes : List (List Bool)} {a b : Data}
    (h : RecordPrograms.Visits (fun key => decide (key = query)) (effect query) nodes a b) :
    b.stacks 6 = List.replicate (nodes.idxOf query) true ++ a.stacks 6 := by
  induction h with
  | nil base => simp
  | @hit key rest base next ht he =>
      have hkey : key = query := of_decide_eq_true ht
      subst key
      simpa [effect] using he
  | @miss key rest base middle next ht he hrest ih =>
      have hkey : key ≠ query := of_decide_eq_false ht
      rw [ih]
      simp only [effect,ite_eq_right hkey] at he
      rw [he]
      simp only [List.idxOf_cons,cond_eq_if,beq_iff_eq,ite_eq_right hkey,
        List.replicate_succ',List.append_assoc,List.singleton_append]

theorem unread_length (query : List Bool) (nodes : List (List Bool)) :
    (RecordPrograms.unread (fun key => decide (key = query)) nodes []).length ≤
      (ProgramEncoding.encodeRecords nodes).length := by
  induction nodes with
  | nil => simp [RecordPrograms.unread,ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons key rest ih =>
      simp only [RecordPrograms.unread]
      split
      · simp only [List.append_nil,ProgramEncoding.encodeRecords,
          Encoding.length_encodeList_cons,id_eq]
        omega
      · change _ ≤ (Encoding.encodeList id (key :: rest)).length
        rw [Encoding.length_encodeList_cons]
        exact ih.trans (by dsimp [ProgramEncoding.encodeRecords]; omega)

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan

theorem register_injective : Function.Injective register := Fin.castAdd_injective _ _
theorem stack_injective : Function.Injective stack := by decide

end Scan
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupFoundCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The existing full-record scanner retains its successful-match bit. This
module exposes that bit without changing the machine or adding instructions. -/
namespace SubexponentialSAT.SubexpNodeIndexProgram.Internal
open BitProgram StructuredCalls SubexpScanPrimitives

theorem any_equal_mem (nodes : List (List Bool)) (query : List Bool) :
    nodes.any (fun key => decide (key=query))=decide (query ∈ nodes) := by
  induction nodes with
  | nil => rfl
  | cons a as ih =>
      by_cases h : a=query
      · subst a; simp
      · simp [h,Ne.symm h,ih]

theorem command_eval_found (regs : Fin 5 → Bool) (query : List Bool) (nodes : List (List Bool)) :
    ∃ n, n + 1 ≤ budget query nodes ∧ ∃ regs',
      Eval command n (state regs query (ProgramEncoding.encodeRecords nodes) [] [] [] [] [])
        (state regs' query (ProgramEncoding.encodeRecords nodes) [] [] [] []
          (List.replicate (nodes.idxOf query) true)) ∧
      regs' 4=decide (query ∈ nodes) := by
  let master := ProgramEncoding.encodeRecords nodes
  let d := state regs query master [] [] [] [] []
  let rr := readRegs regs 0 1 none
  have hc := copy_eval d 1 2 5 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hcEnd : afterCopy d 1 2 0 1 = state rr query master master [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,afterCopy,StackRoutines.copyStacks,state,store]
  have hcLen : (d.stacks 1).length = master.length := rfl
  rw [hcEnd,hcLen] at hc
  let base := state rr query master [] [] [] [] []
  obtain ⟨ns,next,hns,hnext,hvis,hs⟩ := RecordPrograms.iterate_run_with ports callback
    (fun key => decide (key = query)) (callbackCost query) (invariant query master)
    (effect query) (callback_contract query master) nodes [] base ⟨rr,[],rfl⟩
      (rr 0) (rr 1) (rr 4)
  have hcount := visits_count query hvis
  obtain ⟨rs,count,hnext⟩ := hnext
  rw [hnext] at hs hcount
  have hcount' : count = List.replicate (nodes.idxOf query) true := by
    change count = List.replicate (nodes.idxOf query) true ++ [] at hcount
    simpa only [List.append_nil] using hcount
  subst count
  let tail := RecordPrograms.unread (fun key => decide (key = query)) nodes []
  let rs' := normalized rs false true (nodes.any (fun key => decide (key = query)))
  have hs' : Eval (RecordPrograms.iterate ports callback) ns
      (state rr query master master [] [] [] [])
      (state rs' query master tail [] [] [] (List.replicate (nodes.idxOf query) true)) := by
    simpa only [base,outer_state,normalized_self,List.append_nil,master,
      ProgramEncoding.encodeRecords,rs',tail] using hs
  let e := state rs' query master tail [] [] [] (List.replicate (nodes.idxOf query) true)
  have hz := clear_eval e 2
  have hzEnd : cleared e 2 = state (readRegs rs' 0 1 none) query master [] [] [] []
      (List.replicate (nodes.idxOf query) true) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [e,cleared,state,store]
  have hzLen : (e.stacks 2).length = tail.length := rfl
  rw [hzEnd,hzLen] at hz
  have htail := unread_length query nodes
  have hcost := RecordPrograms.program_budget_le_input (callbackCost query) nodes
    20 (9*query.length+32) (fun key _ => by simp [callbackCost,Nat.add_assoc])
  refine ⟨(7*master.length+5)+(ns+(2*tail.length+3)),?_,readRegs rs' 0 1 none,?_,?_⟩
  · change tail.length ≤ master.length at htail
    change 4 + RecordPrograms.budget (callbackCost query) nodes ≤
      (20+(9*query.length+32)+17)*(master.length+1) at hcost
    unfold budget
    change _ ≤ (9*query.length+80)*(master.length+1)
    nlinarith
  · exact hc.seq (hs'.seq hz)

  · simpa [readRegs,rs',normalized] using any_equal_mem nodes query

end SubexponentialSAT.SubexpNodeIndexProgram.Internal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupFound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The same frozen pair-lookup program exposes its native found bit in register4.
No extra scan, metadata value, or runtime instruction is introduced. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan
theorem command_eval_found_oai (regs : Fin 16 → Bool) (literal ambient factor query : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ SubexpNodeIndexProgram.Internal.budget query nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] query [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] []) ∧
      rf 4=decide (query ∈ nodes) := by
  let d := data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
    [] [] query [] [] [] [] []
  let rr := fun i => regs (register i)
  obtain ⟨n,hn,rs,he,hflag⟩ := SubexpNodeIndexProgram.Internal.command_eval_found rr query nodes
  have ha : projectState register stack d =
      SubexpNodeIndexProgram.Internal.state rr query
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [←ha] at he
  have hh := eval_liftCommand_from_state SubexpNodeIndexProgram.Internal.command 0 6
    register stack d register_injective stack_injective he
  let e := embedState register stack d
    (SubexpNodeIndexProgram.Internal.state rs query (ProgramEncoding.encodeRecords nodes)
      [] [] [] [] (List.replicate (nodes.idxOf query) true))
  have hb : e = data e.regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
      (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] [] := by
    apply embedState_eq register stack register_injective stack_injective
    · intro i
      exact embedState_register register stack d _ register_injective i
    · intro i; fin_cases i <;> rfl
    · intro i hi
      exact embedState_register_frame register stack d _ i hi
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi ⟨0,rfl⟩)
        | exact False.elim (hi ⟨1,rfl⟩)
        | exact False.elim (hi ⟨2,rfl⟩)
        | exact False.elim (hi ⟨3,rfl⟩)
        | exact False.elim (hi ⟨4,rfl⟩)
        | exact False.elim (hi ⟨5,rfl⟩)
        | exact False.elim (hi ⟨6,rfl⟩)
  refine ⟨n+1,hn,e.regs,?_,?_⟩
  · change Eval command (n+1) d e at hh
    rw [hb] at hh
    exact hh
  · have hg : e.regs (register 4)=rs 4 :=
      embedState_register register stack d _ register_injective 4
    exact hg.trans hflag

end Scan

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found_oai
