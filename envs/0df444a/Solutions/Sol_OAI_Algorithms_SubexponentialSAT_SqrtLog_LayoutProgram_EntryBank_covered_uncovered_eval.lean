-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:21:30.983377+00:00
-- url     : https://prove2.me/submissions/cefad279-9e2b-47b4-a199-1a0657baf298

import Mathlib
import Definitions.Def_OAIQ081S174

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

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCovered
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

private theorem zero_cleanup (a : Data) (h : MetadataReady a)
    (hp : a.stacks 254=[]) (hn : a.stacks 255=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a
      (finish a (Staging.result 0 1 cleanupOps a).regs ([],[])) := by
  have he := cleanup_eval a (h 199 (by decide) (Or.inr (by decide)))
  have hh : Staging.result 0 1 cleanupOps a=
      finish a (Staging.result 0 1 cleanupOps a).regs ([],[]) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      calc
        (Staging.result 0 1 cleanupOps a).stacks j =
            if j.val < 200 then [] else a.stacks j := cleanup_stacks a j
        _ = (finish a (Staging.result 0 1 cleanupOps a).regs ([],[])).stacks j := by
          by_cases h255 : j=255
          · subst j; simp [finish,hn]
          · by_cases h254 : j=254
            · subst j; simp [finish,hp]
            · simp [finish,h255,h254]
  rw [hh] at he
  exact he

/-- No arithmetic is run when the selected row is covered and the selected
column is outside the covered blocks. Metadata cleanup is still charged. -/
theorem covered_uncovered_eval_oai (a : Data) (h : MetadataReady a)
    (hp : a.stacks 254=[]) (hn : a.stacks 255=[])
    (h5 : a.regs 5=false) :
    ∃ n ≤ 2*metadataFieldsLength a+601, ∃ rf,
      Eval (.seq covered cleanup) n a (finish a rf ([],[])) := by
  have hc := cleanup_metadata_cost a h
  refine ⟨1+Staging.cost 0 1 cleanupOps a,by omega,
    (Staging.result 0 1 cleanupOps a).regs,?_⟩
  exact (Eval.ite_false (yes:=.seq compareBlocks (.ite 7
    (.seq prepare (.seq integer exportPair)) (.base .skip))) h5
    (Eval.base (StructuredProgram.Eval.skip a))).seq (zero_cleanup a h hp hn)

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval_oai
