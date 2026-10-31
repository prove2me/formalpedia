-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:05:29.345211+00:00
-- url     : https://prove2.me/submissions/9893dd7a-71e5-4236-8e72-a94e8227d7b6

import Mathlib
import Definitions.Def_OAIQ081S137
import Definitions.Def_OAIQ081S156

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

theorem action_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (action v pr tmp op) (actionCost op a) a (actionResult v pr op a) := by
  cases op with
  | copy src dst => exact TupleProgram.copy_eval src dst tmp v pr hv.1 hv.2.1 hv.2.2 hvp a ht
  | clear dst => exact TupleProgram.clear_eval dst v pr a
  | push dst b => exact TupleProgram.pushConst_eval dst v b a

theorem action_temp (v pr : Fin r) (tmp : Fin s)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    (actionResult v pr op a).stacks tmp=[] := by
  cases op with
  | copy src dst => simp [actionResult,StackRoutines.copyStacks,hv.2.2,ht]
  | clear dst => by_cases h : tmp=dst <;> simp [actionResult,StackRoutines.clearStacks,h,ht]
  | push dst b => simp only [Action.Valid] at hv; simp [actionResult,TupleProgram.pushedState,hv,ht]

theorem sequence_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (ops : List (Action s)) (a : State r s)
    (hv : ∀ op∈ops,op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (sequence v pr tmp ops) (cost v pr ops a) a (result v pr ops a) := by
  induction ops generalizing a with
  | nil => exact .base (.skip _)
  | cons op ops ih =>
    have hop := hv op (by simp)
    exact (action_eval v pr tmp hvp op a hop ht).seq
      (ih (actionResult v pr op a) (fun x hx=>hv x (by simp [hx]))
        (action_temp v pr tmp op a hop ht))

theorem clear_action_result (v pr : Fin r) (a : State r s) (i j : Fin s) :
    (actionResult v pr (.clear i) a).stacks j=if j=i then [] else a.stacks j := by
  simp [actionResult,StackRoutines.clearStacks,Function.update_apply]

theorem result_clears (v pr : Fin r) (ports : List (Fin s)) (a : State r s) (j : Fin s) :
    (result v pr (ports.map Action.clear) a).stacks j=if j∈ports then [] else a.stacks j := by
  induction ports generalizing a with
  | nil => simp [result]
  | cons p ps ih =>
    simp only [List.map_cons,result,ih,clear_action_result,List.mem_cons]
    by_cases hp : j=p <;> by_cases hs : j∈ps <;> simp [hp,hs]

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

theorem pop_eval (src : Fin 32) (d : Data) (bit : Bool) (tail : List Bool)
    (hs : d.stacks src = bit :: tail) : Eval (pop src) 1 d (popped src bit tail d) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop src 7 0) d
  simpa [pop, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hs] using Eval.base h

theorem smallRegs_ne_six (i : Fin 5) : smallRegs i ≠ 6 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 6 at hv
  omega

theorem sealCall_eval (d : Data) :
    ∃ n e, n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 20 ∧
      Eval sealCall n d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 17 []) 28 [])
        27 (decide (d.stacks 17 = d.stacks 28) :: d.stacks 27) ∧
      e.regs 6 = d.regs 6 := by
  let a := projectState smallRegs sealPorts d
  obtain ⟨n, hn, he⟩ := CollisionStreamProgram.seal_eval a
  let b := CollisionStreamProgram.sealed a (decide (a.stacks 1 = a.stacks 12))
  let e := embedState smallRegs sealPorts d b
  have hn' : n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 := by
    change n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 at hn
    exact hn
  refine ⟨n + 1, e, by omega,
    eval_liftCommand_from_state CollisionStreamProgram.sealCommand 1 11 smallRegs sealPorts d
      smallRegs.injective sealPorts.injective he, ?_, ?_⟩
  · change Function.extend sealPorts b.stacks d.stacks = _
    dsimp [b, CollisionStreamProgram.sealed]
    rw [ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs sealPorts d smallRegs.injective sealPorts.injective)
    change Function.extend sealPorts a.stacks d.stacks = d.stacks at hb
    rw [hb]
    rfl
  · exact embedState_register_frame smallRegs sealPorts d b 6 (by
      rintro ⟨i, hi⟩
      exact smallRegs_ne_six i hi)

theorem low_ne_high (i j : Fin 32) (hi : i.val < 16) (hj : 16 ≤ j.val) : i ≠ j := by
  intro h
  subst j
  omega

theorem compare_eval (left right : Fin 32) (hl : left.val < 16) (hr : right.val < 16)
    (d : Data) (h17 : d.stacks 17 = []) (h28 : d.stacks 28 = [])
    (h27 : d.stacks 27 = []) (h31 : d.stacks 31 = []) :
    ∃ n e, n ≤ 18 * (d.stacks left).length + 9 * (d.stacks right).length + 31 ∧
      Eval (compare left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 6 = d.regs 6 ∧ e.regs 7 = decide (d.stacks left = d.stacks right) := by
  have hl17 := low_ne_high left 17 hl (by decide)
  have hl31 := low_ne_high left 31 hl (by decide)
  have hr17 := low_ne_high right 17 hr (by decide)
  have hr28 := low_ne_high right 28 hr (by decide)
  have hr31 := low_ne_high right 31 hr (by decide)
  let a := afterCopy d left 17 0 1
  let b := afterCopy a right 28 0 1
  have ha := SubexpScanPrimitives.copy_eval d left 17 31 0 1
    hl17 hl31 (by decide) (by decide) h31
  have hb := SubexpScanPrimitives.copy_eval a right 28 31 0 1
    hr28 hr31 (by decide) (by decide) (by simp [a, afterCopy, StackRoutines.copyStacks, h31])
  have haRight : a.stacks right = d.stacks right := by
    simp [a, afterCopy, StackRoutines.copyStacks, hr17]
  have hb17 : b.stacks 17 = d.stacks left := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h17]
  have hb28 : b.stacks 28 = d.stacks right := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h28, hr17]
  have hb27 : b.stacks 27 = [] := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h27]
  obtain ⟨n, c, hn, hc, hcs, hc6⟩ := sealCall_eval b
  let answer := decide (d.stacks left = d.stacks right)
  have hc27 : c.stacks 27 = [answer] := by simp [hcs, hb17, hb28, hb27, answer]
  let e := popped 27 answer [] c
  have he := pop_eval 27 c answer [] hc27
  refine ⟨(7 * (d.stacks left).length + 5) +
      ((7 * (a.stacks right).length + 5) + (n + 1)), e, ?_,
    ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [haRight, hb17, hb28] at *
    omega
  · funext j
    by_cases hj17 : j = 17 <;> by_cases hj28 : j = 28 <;> by_cases hj27 : j = 27 <;>
      simp [e, popped, hcs, b, a, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, hj17, hj28, hj27, h17, h28, h27]
  · simp [e, popped, readRegs, hc6, b, a, afterCopy]
  · simp [e, popped, readRegs, answer]

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem indexPorts_inj : Function.Injective indexPorts := by decide

theorem cleanupOps_valid : ∀ op∈cleanupOps,op.Valid (199:Fin 256) := by
  intro op hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
  trivial

theorem cleanup_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a (Staging.result 0 1 cleanupOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) cleanupOps a cleanupOps_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and measured-call lemmas used by the concrete entry-bank program.
The state maps below only specify the outcomes of actual fixed commands. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem compare_lifted {S : ℕ} (ports : Fin 32 → Fin S)
    (hp : Function.Injective ports) (a : State 16 S)
    (h17 : a.stacks (ports 17)=[]) (h28 : a.stacks (ports 28)=[])
    (h27 : a.stacks (ports 27)=[]) (h31 : a.stacks (ports 31)=[]) :
    ∃ n ≤ 18*(a.stacks (ports 0)).length+9*(a.stacks (ports 1)).length+32,
      ∃ e : State 16 S,
      Eval (liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id ports) n a e ∧
      e.stacks=a.stacks ∧ e.regs 6=a.regs 6 ∧
      e.regs 7=decide (a.stacks (ports 0)=a.stacks (ports 1)) := by
  let p := projectState id ports a
  obtain ⟨n,b,hn,he,hbs,h6,h7⟩ := GlobalBasisEntryCore.compare_eval 0 1
    (by decide) (by decide) p h17 h28 h27 h31
  let e := embedState id ports a b
  refine ⟨n+1,by simpa [p,projectState] using Nat.add_le_add_right hn 1,e,
    eval_liftCommand_from_state _ 0 1 id ports a Function.injective_id hp he,?_,?_,?_⟩
  · change Function.extend ports b.stacks a.stacks=a.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id ports a Function.injective_id hp)
  · exact (embedState_register id ports a b Function.injective_id 6).trans h6
  · exact (embedState_register id ports a b Function.injective_id 7).trans h7

/-- Every clear is charged, even when a repeated port is already empty. -/
theorem clear_cost_le {r s : ℕ} (v pr : Fin r) (ports : List (Fin s))
    (a : State r s) :
    Staging.cost v pr (ports.map Staging.Action.clear) a ≤
      2*(ports.map (fun j => (a.stacks j).length)).sum+3*ports.length := by
  induction ports generalizing a with
  | nil => simp [Staging.cost]
  | cons j js ih =>
    let b := Staging.actionResult v pr (.clear j) a
    have hb : ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
      intro i
      simp only [b,Staging.clear_action_result]
      split_ifs <;> simp
    have hsum' : (js.map (fun i => (b.stacks i).length)).sum ≤
        (js.map (fun i => (a.stacks i).length)).sum := by
      clear ih
      induction js with
      | nil => simp
      | cons i is hi => simpa using Nat.add_le_add (hb i) hi
    have h := ih b
    dsimp only [b] at h hsum'
    simp only [List.map_cons,Staging.cost,Staging.actionCost,List.sum_cons,List.length_cons]
    omega

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem compareIndices_eval (a : Data) (h : ∀ j : Fin 256, j.val < 30 → a.stacks j=[]) :
    ∃ n ≤ 18*(a.stacks 252).length+9*(a.stacks 253).length+32,
      ∃ e : Data, Eval compareIndices n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 252=a.stacks 253) :=
  EntryBankFrame.compare_lifted indexPorts indexPorts_inj a
    (h _ (by decide)) (h _ (by decide)) (h _ (by decide)) (h _ (by decide))

theorem workPorts_mem (j : Fin 256) : j∈workPorts ↔ j.val < 200 := by
  simp only [workPorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val=j.val at hv
    omega
  · intro hj
    exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩

theorem workPorts_length : workPorts.length=200 :=
  List.length_ofFn

theorem cleanup_stacks (a : Data) (j : Fin 256) :
    (Staging.result 0 1 cleanupOps a).stacks j=if j.val < 200 then [] else a.stacks j := by
  simpa only [cleanupOps,workPorts_mem] using Staging.result_clears 0 1 workPorts a j

theorem cleanup_cost (a : Data) :
    Staging.cost 0 1 cleanupOps a ≤
      2*(workPorts.map (fun j => (a.stacks j).length)).sum+600 := by
  convert EntryBankFrame.clear_cost_le 0 1 workPorts a using 1 <;>
    norm_num [cleanupOps,workPorts_length]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem metadataFieldsLength_eq (a : Data) : metadataFieldsLength a=
    (a.stacks 64).length+(a.stacks 65).length+(a.stacks 66).length+
    (a.stacks 67).length+(a.stacks 68).length+(a.stacks 69).length := by
  simp [metadataFieldsLength,metadataIndices]
  omega

theorem work_sum_metadata (a : Data) (h : MetadataReady a) :
    (workPorts.map (fun j => (a.stacks j).length)).sum=metadataFieldsLength a := by
  simp only [workPorts,List.map_ofFn,List.sum_ofFn,Function.comp_def,metadataFieldsLength]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hi' : (i.val < 64) ∨ (70 ≤ i.val) := by
    by_contra hn
    have hx : i.val=64 ∨ i.val=65 ∨ i.val=66 ∨ i.val=67 ∨ i.val=68 ∨ i.val=69 := by omega
    rcases hx with hx|hx|hx|hx|hx|hx
    all_goals
      apply hi
      simp only [metadataIndices,Finset.mem_insert,Finset.mem_singleton]
      first | exact Or.inl (Fin.ext hx)
            | exact Or.inr (Or.inl (Fin.ext hx))
            | exact Or.inr (Or.inr (Or.inl (Fin.ext hx)))
            | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hx))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hx)))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext hx)))))
  simpa using congrArg List.length (h (i.castAdd 56) i.isLt hi')

theorem cleanup_metadata_cost (a : Data) (h : MetadataReady a) :
    Staging.cost 0 1 cleanupOps a ≤ 2*metadataFieldsLength a+600 := by
  simpa only [work_sum_metadata a h] using cleanup_cost a

/-- The uncovered row branch is an actual comparison, conditional push, and
cleanup. It needs no coverage semantics: those are supplied by the caller. -/
theorem uncovered_cleanup_eval_oai (a : Data) (h : MetadataReady a)
    (h254 : a.stacks 254=[]) :
    ∃ n ≤ 27*((a.stacks 252).length+(a.stacks 253).length)+
        2*metadataFieldsLength a+635,
      ∃ z : Data, Eval (.seq uncovered cleanup) n a z ∧
      (∀ j : Fin 256, z.stacks j=
        if j.val < 200 then [] else if j=254 then
          (if a.stacks 252=a.stacks 253 then [true] else []) else a.stacks j) := by
  obtain ⟨nc,hnc,b,he,hbs,_,h7⟩ := compareIndices_eval a
    (fun j hj => h j (by omega) (Or.inl (by omega)))
  have hbt : b.stacks 199=[] := by rw [hbs]; exact h 199 (by decide) (Or.inr (by decide))
  have hbready : MetadataReady b := by intro j hj hk; rw [hbs]; exact h j hj hk
  have hbmass : metadataFieldsLength b=metadataFieldsLength a := by
    simp only [metadataFieldsLength,hbs]
  by_cases heq : a.stacks 252=a.stacks 253
  · let c := TupleProgram.pushedState (254 : Fin 256) (0 : Fin 16) true b
    have hp := TupleProgram.pushConst_eval (254 : Fin 256) (0 : Fin 16) true b
    have hcst : c.stacks=Function.update a.stacks 254 [true] := by
      simp [c,hbs,h254]
    have hct : c.stacks 199=[] := by simp [hcst]; exact h 199 (by decide) (Or.inr (by decide))
    have hcready : MetadataReady c := by
      intro j hj hk
      have hn : j≠254 := by intro hz; subst j; norm_num at hj
      simpa [hcst,hn] using h j hj hk
    have hcmass : metadataFieldsLength c=metadataFieldsLength a := by
      simp [metadataFieldsLength_eq,hcst]
    have hc := cleanup_metadata_cost c hcready
    have hbranch := Eval.ite_true (no := (.base .skip : Code))
      (show b.regs 7=true by simp [h7,heq]) hp
    refine ⟨nc+3+Staging.cost 0 1 cleanupOps c,?_,Staging.result 0 1 cleanupOps c,
      (he.seq hbranch).seq (cleanup_eval c hct),?_⟩
    · rw [hcmass] at hc
      omega
    · intro j
      rw [cleanup_stacks,hcst]
      simp [heq,Function.update_apply]
  · have hc := cleanup_metadata_cost b hbready
    have hbranch := Eval.ite_false (yes := (TupleProgram.pushConst 254 0 true : Code))
      (show b.regs 7=false by simp [h7,heq]) (Eval.base (StructuredProgram.Eval.skip b))
    refine ⟨nc+1+Staging.cost 0 1 cleanupOps b,?_,Staging.result 0 1 cleanupOps b,
      (he.seq hbranch).seq (cleanup_eval b hbt),?_⟩
    · rw [hbmass] at hc
      omega
    · intro j
      rw [cleanup_stacks,hbs]
      by_cases hj : j=254
      · subst j; simp [heq,h254]
      · simp [hj]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval_oai
