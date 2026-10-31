-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:21:33.020833+00:00
-- url     : https://prove2.me/submissions/35776ac9-d16b-4ba8-8230-1be9e624ae45

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

theorem action_frame (v pr : Fin r) (op : Action s) (a : State r s)
    (j : Fin s) (hj : j≠op.destination) :
    (actionResult v pr op a).stacks j=a.stacks j := by
  cases op <;> simp_all [Action.destination,actionResult,StackRoutines.copyStacks,
    StackRoutines.clearStacks,TupleProgram.pushedState]

theorem result_frame (v pr : Fin r) (ops : List (Action s)) (a : State r s)
    (j : Fin s) (hj : ∀ op∈ops,j≠op.destination) :
    (result v pr ops a).stacks j=a.stacks j := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (actionResult v pr op a) (fun x hx=>hj x (by simp [hx]))).trans
      (action_frame v pr op a j (hj op (by simp)))

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

theorem integerRegs_inj : Function.Injective integerRegs := Fin.castAdd_injective _ _
theorem integerPorts_inj : Function.Injective integerPorts := Fin.castAdd_injective _ _

theorem prepareOps_valid : ∀ op∈prepareOps,op.Valid (199:Fin 256) := by decide
theorem exportOps_valid : ∀ op∈exportOps,op.Valid (199:Fin 256) := by decide
theorem cleanupOps_valid : ∀ op∈cleanupOps,op.Valid (199:Fin 256) := by
  intro op hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
  trivial

theorem prepare_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval prepare (Staging.cost 0 1 prepareOps a) a (Staging.result 0 1 prepareOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) prepareOps a prepareOps_valid ht

theorem exportPair_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval exportPair (Staging.cost 0 1 exportOps a) a (Staging.result 0 1 exportOps a) :=
  Staging.sequence_eval 0 1 199 (by decide) exportOps a exportOps_valid ht

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

theorem staging_result_temp {r s : ℕ} (v pr : Fin r) (tmp : Fin s)
    (ops : List (Staging.Action s)) (a : State r s)
    (hv : ∀ op∈ops,op.Valid tmp) (ht : a.stacks tmp=[]) :
    (Staging.result v pr ops a).stacks tmp=[] := by
  induction ops generalizing a with
  | nil => exact ht
  | cons op ops ih =>
    exact ih (Staging.actionResult v pr op a)
      (fun x hx => hv x (by simp [hx]))
      (Staging.action_temp v pr tmp op a (hv op (by simp)) ht)

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

theorem prepare_frame (a : Data) (j : Fin 256) (hj : 64 ≤ j.val) :
    (Staging.result 0 1 prepareOps a).stacks j=a.stacks j := by
  apply Staging.result_frame
  intro op hop
  simp only [prepareOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Staging.Action.destination] <;>
    (intro h; have hv := congrArg Fin.val h; simp at hv; omega)

theorem exportPair_stacks (a : Data) (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) :
    (Staging.result 0 1 exportOps a).stacks=
      Function.update (Function.update a.stacks 254 (a.stacks 53)) 255 (a.stacks 54) := by
  simp [exportOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h254,h255]

theorem workPorts_mem (j : Fin 256) : j∈workPorts ↔ j.val < 200 := by
  simp only [workPorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val=j.val at hv
    omega
  · intro hj
    exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩

theorem cleanup_stacks (a : Data) (j : Fin 256) :
    (Staging.result 0 1 cleanupOps a).stacks j=if j.val < 200 then [] else a.stacks j := by
  simpa only [cleanupOps,workPorts_mem] using Staging.result_clears 0 1 workPorts a j

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFramePrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem integer_lifted (a : Data) {n : ℕ} {b : IntegerEntry.Data}
    (he : Eval IntegerEntry.command n (projectState integerRegs integerPorts a) b) :
    Eval integer (n+1) a (embedState integerRegs integerPorts a b) ∧
    (∀ j : Fin 256, 64 ≤ j.val →
      (embedState integerRegs integerPorts a b).stacks j=a.stacks j) := by
  refine ⟨eval_liftCommand_from_state IntegerEntry.command 23 53 integerRegs integerPorts a
    integerRegs_inj integerPorts_inj he,?_⟩
  intro j hj
  apply embedState_stack_frame
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  change i.val=j.val at hv
  omega

/-- Export and cleanup have a single exact endpoint on the entire caller
store, including its unconstrained private bank212..251. -/
theorem export_cleanup_stacks (a : Data) (h254 : a.stacks 254=[])
    (h255 : a.stacks 255=[]) (j : Fin 256) :
    (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps a)).stacks j=
      if j.val < 200 then [] else if j=255 then a.stacks 54
        else if j=254 then a.stacks 53 else a.stacks j := by
  rw [cleanup_stacks,exportPair_stacks a h254 h255]
  simp only [Function.update_apply]

theorem export_cleanup_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval (.seq exportPair cleanup)
      (Staging.cost 0 1 exportOps a+
        Staging.cost 0 1 cleanupOps (Staging.result 0 1 exportOps a))
      a (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps a)) := by
  exact (exportPair_eval a ht).seq
    (cleanup_eval _ (EntryBankFrame.staging_result_temp 0 1 199 exportOps a exportOps_valid ht))

/-- A complete measured inner entry call. The premise is an actual trace of
the fixed integer command, not a supplied value or a free callback. -/
theorem prepared_integer_export_cleanup_oai (a : Data) (ht : a.stacks 199=[])
    (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) {n : ℕ} {b : IntegerEntry.Data}
    (he : Eval IntegerEntry.command n
      (projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)) b) :
    let p := Staging.result 0 1 prepareOps a
    let q := embedState integerRegs integerPorts p b
    let e := Staging.result 0 1 exportOps q
    let z := Staging.result 0 1 cleanupOps e
    Eval (.seq prepare (.seq integer (.seq exportPair cleanup)))
      (Staging.cost 0 1 prepareOps a+
        ((n+1)+(Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e))) a z ∧
    (∀ j : Fin 256, z.stacks j=
      if j.val < 200 then [] else if j=255 then b.stacks 54
        else if j=254 then b.stacks 53 else a.stacks j) := by
  intro p q e z
  obtain ⟨hi,hf⟩ := integer_lifted p he
  have hq : ∀ j : Fin 256, 64 ≤ j.val → q.stacks j=a.stacks j := by
    intro j hj
    exact (hf j hj).trans (prepare_frame a j hj)
  have hqt : q.stacks 199=[] := (hq 199 (by decide)).trans ht
  have hq254 : q.stacks 254=[] := (hq 254 (by decide)).trans h254
  have hq255 : q.stacks 255=[] := (hq 255 (by decide)).trans h255
  refine ⟨(prepare_eval a ht).seq (hi.seq (export_cleanup_eval q hqt)),?_⟩
  intro j
  change (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps q)).stacks j=_
  rw [export_cleanup_stacks q hq254 hq255 j]
  have h53 : q.stacks 53=b.stacks 53 :=
    embedState_stack integerRegs integerPorts p b integerPorts_inj 53
  have h54 : q.stacks 54=b.stacks 54 :=
    embedState_stack integerRegs integerPorts p b integerPorts_inj 54
  rw [h53,h54]
  split_ifs with hj hj255 hj254
  · rfl
  · rfl
  · rfl
  · exact hq j (by omega)

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup_oai
