-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:45:53.984619+00:00
-- url     : https://prove2.me/submissions/a3b3ae20-d5c3-47ee-8556-528b58bf04b4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173

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

theorem sum_map_le_length {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x∈xs,f x ≤ B) : (xs.map f).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      f x+(xs.map f).sum ≤ B+xs.length*B := Nat.add_le_add hx hs
      _ = (xs.length+1)*B := by ring

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

open BitProgram

namespace Literal

theorem prefix_trace (payload out : List Bool) (v p c : Bool) :
    Trace program 3 (cfg (some 0) v p c payload out [])
      (cfg (some 3) false p true payload (false :: out) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, triple]

theorem copy_cycle (b v p : Bool) (bs out scratch : List Bool) :
    Trace program 5 (cfg (some 3) v p true (b :: bs) out scratch)
      (cfg (some 3) b true true bs (b :: true :: out) (b :: scratch)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_finish (v p : Bool) (out scratch : List Bool) :
    Trace program 3 (cfg (some 3) v p true [] out scratch)
      (cfg (some 9) false false true [] (false :: out) scratch) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_trace (payload out scratch : List Bool) (v p : Bool) :
    Trace program (5 * payload.length + 3)
      (cfg (some 3) v p true payload out scratch)
      (cfg (some 9) false false true []
        ((Encoding.frame payload).reverse ++ out) (payload.reverse ++ scratch)) := by
  induction payload generalizing out scratch v p with
  | nil => simpa [Encoding.frame] using copy_finish v p out scratch
  | cons b bs ih =>
      have h := (copy_cycle b v p bs out scratch).trans
        (ih (b :: true :: out) (b :: scratch) b true)
      convert h using 1 <;>
        simp [Encoding.frame, List.reverse_cons, List.append_assoc] ; omega

theorem restore_cycle (b v p : Bool) (bs payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out (b :: bs))
      (cfg (some 9) b true true (b :: payload) out bs) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_finish (v p : Bool) (payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out [])
      (cfg none false false true payload out []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_trace (scratch payload out : List Bool) (v p : Bool) :
    Trace program (3 * scratch.length + 3)
      (cfg (some 9) v p true payload out scratch)
      (cfg none false false true (scratch.reverse ++ payload) out []) := by
  induction scratch generalizing payload v p with
  | nil => simpa using restore_finish v p payload out
  | cons b bs ih =>
      have h := (restore_cycle b v p bs payload out).trans (ih (b :: payload) b true)
      convert h using 1 <;> simp [List.reverse_cons, List.append_assoc] ; omega

/-- Copy a raw literal payload, frame it, and emit its push opcode. The
payload is restored exactly and the scratch port is again empty. -/
theorem trace (payload out : List Bool) (v p c : Bool) :
    Trace program (8 * payload.length + 9)
      (cfg (some 0) v p c payload out [])
      (cfg none false false true payload
        ((false :: Encoding.frame payload).reverse ++ out) []) := by
  have hc := copy_trace payload (false :: out) [] false p
  simp only [List.append_nil] at hc
  have hr := restore_trace payload.reverse []
    ((Encoding.frame payload).reverse ++ false :: out) false false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := (prefix_trace payload out v p c).trans (hc.trans hr)
  convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

end Literal

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid preserving conversion of one scalar word into a complete forward
postfix literal. This is used for uncovered identity entries and zero branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Literal

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (regs : Fin 3 → Bool) (payload : List Bool) :
    ∃ rf, Eval command (14*payload.length+18)
      (state regs payload [] [] [])
      (state rf payload [] [] (SubexpKernelControl.pushWord payload)) := by
  have hr : regs=SubexpHornerProgram.triple (regs 0) (regs 1) (regs 2) := by
    funext j
    fin_cases j <;> rfl
  have ht := SubexpHornerProgram.Literal.trace payload [] (regs 0) (regs 1) (regs 2)
  let a := state regs payload [] [] []
  let b := state (SubexpHornerProgram.triple false false true) payload
    (SubexpKernelControl.pushWord payload).reverse [] []
  have he : Eval callLiteral (8*payload.length+9) a b := by
    have hp : projectState id ports a =
        ⟨SubexpHornerProgram.triple (regs 0) (regs 1) (regs 2),SubexpHornerProgram.triple payload [] []⟩ := by
      apply congrArg₂ StructuredProgram.State.mk hr
      funext j
      fin_cases j <;> rfl
    let target : State 3 3 :=
      ⟨SubexpHornerProgram.triple false false true,
        SubexpHornerProgram.triple payload ((false::Encoding.frame payload).reverse++[]) []⟩
    have ht' : Trace SubexpHornerProgram.Literal.program (8*payload.length+9)
        ((projectState id ports a).withPC (some SubexpHornerProgram.Literal.program.entry))
        (target.withPC none) := by
      rw [hp]
      simpa only [SubexpHornerProgram.Literal.cfg,StructuredProgram.State.withPC,
        SubexpHornerProgram.Literal.program,target] using ht
    have hh := eval_call_from_state SubexpHornerProgram.Literal.program id ports a
      Function.injective_id (Fin.castAdd_injective _ _) ht'
    have hb : embedState id ports a
        ⟨SubexpHornerProgram.triple false false true,
          SubexpHornerProgram.triple payload
            ((false::Encoding.frame payload).reverse++[]) []⟩=b := by
      apply embedState_eq_of_ports id ports _ _ _ Function.injective_id (Fin.castAdd_injective _ _)
      · intro j; rfl
      · intro j hj; exact (hj ⟨j,rfl⟩).elim
      · intro j; fin_cases j <;> simp [b,state,ports,SubexpHornerProgram.triple,SubexpKernelControl.pushWord]
      · intro j hj
        have hj3 : j = 3 := by
          by_contra hn
          have hlt : j.val < 3 := by omega
          exact hj ⟨⟨j.val,hlt⟩,Fin.ext rfl⟩
        subst j
        rfl
    change Eval callLiteral (8*payload.length+9) a (embedState id ports a target) at hh
    change embedState id ports a target=b at hb
    rw [hb] at hh
    exact hh
  have htr := SubexpScanPrimitives.transfer_eval b (1:Fin 4) 3 (0:Fin 3) 1 (by decide) (by decide)
  let e := SubexpScanPrimitives.afterTransfer b 1 3 0 1
  have heq : e=state e.regs payload [] [] (SubexpKernelControl.pushWord payload) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [b,state,StackRoutines.transferStacks]
  have hh := he.seq htr
  change Eval command _ a e at hh
  rw [heq] at hh
  refine ⟨e.regs,?_⟩
  convert hh using 1 ; simp [b,state,SubexpKernelControl.pushWord_length] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Literal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem cleanup_valid : ∀ op∈cleanupOps,op.Valid (319:Fin 320) := by
  intro op hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
  trivial

theorem cleanup_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a (Staging.result 0 1 cleanupOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) cleanupOps a cleanup_valid ht

theorem cleanup_stacks (a : Data) (j : Fin 320) :
    (Staging.result 0 1 cleanupOps a).stacks j=
      if j∈cleanupPorts then [] else a.stacks j :=
  Staging.result_clears 0 1 cleanupPorts a j

theorem cleanup_cost (a : Data) :
    Staging.cost 0 1 cleanupOps a ≤
      2*(cleanupPorts.map (fun j => (a.stacks j).length)).sum+180 := by
  simpa [cleanupOps,cleanupPorts] using EntryBankFrame.clear_cost_le 0 1 cleanupPorts a

theorem cleanup_cost_le (a : Data) (B : ℕ)
    (h : ∀ j∈cleanupPorts,(a.stacks j).length ≤ B) :
    Staging.cost 0 1 cleanupOps a ≤ 120*B+180 := by
  have hs := EntryBankFrame.sum_map_le_length cleanupPorts (fun j => (a.stacks j).length) B h
  have hc := cleanup_cost a
  have hl : cleanupPorts.length=60 := by simp [cleanupPorts]
  rw [hl] at hs
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem literalRegs_inj : Function.Injective literalRegs := Fin.castAdd_injective _ _

theorem literal_eval (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
    (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[]) (h287 : a.stacks 287=[]) :
    ∃ b : Data, Eval (literal src) (14*(a.stacks src).length+19) a b ∧
      b.stacks=Function.update a.stacks 287 (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
  have hp : Function.Injective (literalPorts src) := by
    rcases hsrc with rfl|rfl <;> decide
  let small := projectState literalRegs (literalPorts src) a
  have hi : small=Literal.state (a.regs ∘ literalRegs) (a.stacks src) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [literalPorts,h315,h316,h287]
  obtain ⟨rf,he⟩ := Literal.command_eval (a.regs ∘ literalRegs) (a.stacks src)
  rw [← hi] at he
  let z := Literal.state rf (a.stacks src) [] [] (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src))
  have hz : z.stacks=Function.update small.stacks 3 (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
    rw [hi]
    funext j
    fin_cases j <;> simp [z,Literal.state]
  let b := embedState literalRegs (literalPorts src) a z
  refine ⟨b,?_,?_⟩
  · exact eval_liftCommand_from_state Literal.command 0 3 literalRegs (literalPorts src) a literalRegs_inj hp he
  · change Function.extend (literalPorts src) z.stacks a.stacks=_
    rw [hz,ProgramLinking.extend_update hp]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project literalRegs (literalPorts src) a literalRegs_inj hp)
    change Function.extend (literalPorts src) small.stacks a.stacks=a.stacks at hh
    rw [hh]
    rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition for the actual SourceBank. Premises about table and mismatch
execution are traces of their fixed native programs, not free callbacks. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem literal_cleanup_eval_oai (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
    (ht : a.stacks 319=[]) (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[])
    (h287 : a.stacks 287=[]) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 14*(a.stacks src).length+19+120*B+180,
      ∃ b : Data, Eval (.seq (literal src) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287
          (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
  obtain ⟨b,hb,hbs⟩ := literal_eval src hsrc a h315 h316 h287
  have hbt : b.stacks 319=[] := by simp [hbs,ht]
  have hc : Staging.cost 0 1 cleanupOps b ≤ 120*B+180 := by
    apply cleanup_cost_le
    intro j hj
    have hne : j≠287 := by intro h; subst j; exact (by decide : (287:Fin 320)∉cleanupPorts) hj
    simpa [hbs,hne] using hB j
  refine ⟨14*(a.stacks src).length+19+Staging.cost 0 1 cleanupOps b,by omega,
    Staging.result 0 1 cleanupOps b,hb.seq (cleanup_eval b hbt),?_⟩
  funext j
  rw [cleanup_stacks,hbs]
  by_cases hj : j=287
  · subst j; simp [cleanupPorts]
  · simp [clearedStacks,hj]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval_oai
