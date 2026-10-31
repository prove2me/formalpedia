-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:40:03.208628+00:00
-- url     : https://prove2.me/submissions/b54e599f-6b14-4ed2-9de5-1910702c92ec

import Mathlib
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_emit_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_TypeCompare_command_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageEmitter_valid : ∀ op∈stageEmitterOps,op.Valid (319:Fin 320) := by decide

theorem stageEmitter_eval (a : Data) (ht : a.stacks 319=[]) :
    Eval stageEmitter (Staging.cost 0 1 stageEmitterOps a) a (Staging.result 0 1 stageEmitterOps a) :=
  Staging.sequence_eval 0 1 319 (by decide) stageEmitterOps a stageEmitter_valid ht

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured native stages used by the packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem lowRegs_inj : Function.Injective lowRegs := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

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

theorem stageEmitter_stacks (a : Data)
    (h : ∀ j∈emitterDestinations,a.stacks j=[]) :
    (Staging.result 0 1 stageEmitterOps a).stacks=emitterStacks a := by
  have h280 := h 280 (by simp [emitterDestinations])
  have h281 := h 281 (by simp [emitterDestinations])
  have h282 := h 282 (by simp [emitterDestinations])
  have h283 := h 283 (by simp [emitterDestinations])
  have h284 := h 284 (by simp [emitterDestinations])
  have h285 := h 285 (by simp [emitterDestinations])
  have h286 := h 286 (by simp [emitterDestinations])
  have h259 := h 259 (by simp [emitterDestinations])
  have h266 := h 266 (by simp [emitterDestinations])
  have h269 := h 269 (by simp [emitterDestinations])
  simp [stageEmitterOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,
    emitterStacks,h280,h281,h282,h283,h284,h285,h286,h259,h266,h269]

theorem stageEmitter_cost (a : Data) :
    Staging.cost 0 1 stageEmitterOps a=7*emitterSize a+50 := by
  simp [stageEmitterOps,Staging.cost,Staging.actionCost,Staging.actionResult,
    StackRoutines.copyStacks,emitterSize]
  ring

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

theorem lowPorts_inj : Function.Injective lowPorts := Fin.castAdd_injective _ _

theorem compareTypes_eval (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
    ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+35,
      ∃ e : Data, Eval compareTypes n a e ∧ e.stacks=a.stacks ∧
        e.regs 7=decide (a.stacks 23=a.stacks 24) := by
  let p := projectState lowRegs lowPorts a
  obtain ⟨n,hn,b,he,hbs,h7⟩ := TypeCompare.command_eval p h0 h1 h2 h3
  let e := embedState lowRegs lowPorts a b
  have hh := eval_liftCommand_from_state TypeCompare.command 23 23 lowRegs lowPorts a
    lowRegs_inj lowPorts_inj he
  refine ⟨n+1,by simpa [p,projectState,lowPorts] using Nat.add_le_add_right hn 1,e,hh,?_,?_⟩
  · change Function.extend lowPorts b.stacks a.stacks=a.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks (embedState_project lowRegs lowPorts a lowRegs_inj lowPorts_inj)
  · exact (embedState_register lowRegs lowPorts a b lowRegs_inj 7).trans h7

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem emitterClean_destinations (a : Data) (h : EmitterClean a) :
    ∀ j∈emitterDestinations,a.stacks j=[] := by
  intro j hj
  simp only [emitterDestinations,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact h _ (by decide) (by decide) (by decide)

theorem stageEmitter_ready (a : Data) (hclean : EmitterClean a)
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth) :
    UniversalRowLoop.ready tables width rowWidth positions
      (projectState emitterRegs emitterPorts (Staging.result 0 1 stageEmitterOps a)) := by
  have hs := stageEmitter_stacks a (emitterClean_destinations a hclean)
  have hfield (j : Fin 32) :
      (projectState emitterRegs emitterPorts (Staging.result 0 1 stageEmitterOps a)).stacks j=
        emitterStacks a (emitterPorts j) := congrFun hs _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hv
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hi
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hn
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hr
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hp
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hw
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hrw
  · rw [hfield]
    simp [emitterStacks,emitterPorts,UniversalRowFactorLoop.indexWord,
      hclean 272 (by decide) (by decide) (by decide)]
  · intro j hj
    rw [hfield]
    fin_cases j <;> simp_all [emitterStacks,emitterPorts,EmitterClean]

theorem prepend_cleanup {first second : Code} {n m : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval (.seq second cleanup) m b c) :
    Eval (.seq (.seq first second) cleanup) (n+m) a c := by
  cases hs with
  | seq hg hc => simpa [Nat.add_assoc] using (hf.seq hg).seq hc

theorem cleanup_emitter_stacks (a b : Data) (word : List Bool)
    (hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word) :
    (Staging.result 0 1 cleanupOps b).stacks=Function.update (clearedStacks a) 287 word := by
  funext j
  rw [cleanup_stacks,hb]
  by_cases hj : j=287
  · subst j; simp [cleanupPorts]
  · by_cases hc : j∈cleanupPorts
    · simp [hc,hj,clearedStacks]
    · have hn (i : Fin 320) (hi : i∈cleanupPorts) : j≠i := by
        intro h; subst j; exact hc hi
      simp [hc,hj,clearedStacks,emitterStacks,
        hn 274 (by decide),hn 280 (by decide),hn 281 (by decide),hn 282 (by decide),
        hn 283 (by decide),hn 284 (by decide),hn 285 (by decide),hn 286 (by decide),
        hn 259 (by decide),hn 266 (by decide),hn 269 (by decide)]

theorem emitterStacks_length_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B)
    (j : Fin 320) : (emitterStacks a j).length ≤ B := by
  have upd (f : Fin 320 → List Bool) (hf : ∀ i,(f i).length ≤ B)
      (k : Fin 320) (v : List Bool) (hv : v.length ≤ B) :
      ∀ i,(Function.update f k v i).length ≤ B := by
    intro i
    by_cases hi : i=k
    · subst i; simpa using hv
    · simpa [hi] using hf i
  have h280 := upd _ hB 280 _ (hB 67)
  have h281 := upd _ h280 281 _ (hB 308)
  have h282 := upd _ h281 282 _ (hB 309)
  have h283 := upd _ h282 283 _ (hB 310)
  have h284 := upd _ h283 284 _ (hB 71)
  have h285 := upd _ h284 285 _ (hB 311)
  have h286 := upd _ h285 286 _ (hB 312)
  have h259 := upd _ h286 259 _ (hB 313)
  have h266 := upd _ h259 266 _ (hB 314)
  exact upd _ h266 269 _ (hB 47) j

theorem cleanup_emitter_cost (a b : Data) (word : List Bool) (B : ℕ)
    (hB : ∀ j,(a.stacks j).length ≤ B)
    (hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word) :
    Staging.cost 0 1 cleanupOps b ≤ 120*B+180 := by
  apply cleanup_cost_le
  intro j hj
  have hn : j≠287 := by intro h; subst j; exact (by decide : (287:Fin 320)∉cleanupPorts) hj
  rw [hb]
  rw [Function.update_of_ne hn]
  by_cases he : j=274
  · subst j; simp
  · simpa [Function.update_of_ne he] using emitterStacks_length_le a B hB j

/-- The prepared emitter is called physically and its workspace is cleared.
The scalar cache words remain input data, not an input polynomial oracle. -/
theorem stage_emit_cleanup_eval (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    let word := UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314)
      (a.stacks 313++a.stacks 314)
      (UniversalRowDataProgram.row tables positions (a.stacks 274) (a.stacks 47))
    ∃ n ≤ 7*emitterSize a+50+
      UniversalRowSourceProgram.bound tables width rowWidth positions
        (a.stacks 274) (a.stacks 47) (a.stacks 313) (a.stacks 314)+120*B+180,
      ∃ b : Data, Eval (.seq (.seq stageEmitter emit) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 word := by
  intro word
  let p := Staging.result 0 1 stageEmitterOps a
  have hs : p.stacks=emitterStacks a := stageEmitter_stacks a (emitterClean_destinations a hclean)
  have hready := stageEmitter_ready a hclean tables width rowWidth positions hv hi hn hr hp hw hrw
  obtain ⟨ne,hne,b,he,hbs⟩ := emit_eval tables width rowWidth positions valid
    (a.stacks 274) (a.stacks 47) (a.stacks 313) (a.stacks 314) p hready
    (by simp [hs,emitterStacks]) (by simp [hs,emitterStacks])
    (by simp [hs,emitterStacks]) (by simp [hs,emitterStacks])
    (by simpa [hs,emitterStacks] using hclean 270 (by decide) (by decide) (by decide))
    (by simpa [hs,emitterStacks] using hclean 273 (by decide) (by decide) (by decide))
    (by simpa [hs,emitterStacks] using hclean 287 (by decide) (by decide) (by decide))
  have hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word := by
    simpa only [hs,word] using hbs
  have hbt : b.stacks 319=[] := by
    simp [hb,emitterStacks,ht]
  have hc := cleanup_emitter_cost a b word B hB hb
  refine ⟨Staging.cost 0 1 stageEmitterOps a+(ne+Staging.cost 0 1 cleanupOps b),?_,
    Staging.result 0 1 cleanupOps b,
    by simpa [Nat.add_assoc] using ((stageEmitter_eval a ht).seq he).seq (cleanup_eval b hbt),
    cleanup_emitter_stacks a b word hb⟩
  rw [stageEmitter_cost]
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem delta_eval (a : Data) (ht : a.stacks 319=[]) (he : a.stacks 274=[]) :
    let word := if a.regs 7 then a.stacks 314 else a.stacks 313
    ∃ b : Data, Eval delta (7*word.length+6) a b ∧
      b.stacks=Function.update a.stacks 274 word := by
  intro word
  cases hf : a.regs 7 with
  | false =>
      let b := Staging.actionResult 0 1 (.copy 313 274) a
      have h := Staging.action_eval 0 1 319 (by decide) (.copy 313 274) a (by decide) ht
      refine ⟨b,?_,?_⟩
      · simpa [delta,word,hf,Staging.actionCost] using
          (Eval.ite_false (yes:=Staging.action 0 1 319 (.copy 314 274)) hf h)
      · simp [b,word,hf,Staging.actionResult,StackRoutines.copyStacks,he]
  | true =>
      let b := Staging.actionResult 0 1 (.copy 314 274) a
      have h := Staging.action_eval 0 1 319 (by decide) (.copy 314 274) a (by decide) ht
      refine ⟨b,?_,?_⟩
      · simpa [delta,word,hf,Staging.actionCost] using
          (Eval.ite_true (no:=Staging.action 0 1 319 (.copy 313 274)) hf h)
      · simp [b,word,hf,Staging.actionResult,StackRoutines.copyStacks,he]

theorem clearedStacks_eq (a b : Data)
    (h : ∀ j,j∉cleanupPorts → b.stacks j=a.stacks j) : clearedStacks b=clearedStacks a := by
  funext j
  by_cases hj : j∈cleanupPorts <;> simp [clearedStacks,hj,h]

theorem finish_universal_eval_oai (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
    (h274 : a.stacks 274=[]) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ finishBound tables width rowWidth positions a B,
      ∃ b : Data, Eval (.seq (.seq compareTypes (.seq delta (.seq stageEmitter emit))) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 (sourceWord tables positions a) := by
  obtain ⟨nc,hnc,b,hc,hbs,h7⟩ := compareTypes_eval a h0 h1 h2 h3
  obtain ⟨c,hd,hcs⟩ := delta_eval b (by simpa [hbs] using ht) (by simpa [hbs] using h274)
  have hdw : (if b.regs 7 then b.stacks 314 else b.stacks 313)=deltaWord a := by
    simp [h7,hbs,deltaWord]
  rw [hdw] at hd hcs
  rw [hbs] at hcs
  have hcl : EmitterClean c := by
    intro j hj hk hne
    simpa [hcs,hne] using hclean j hj hk hne
  have hcb : ∀ j,(c.stacks j).length ≤ B := by
    intro j
    by_cases hj : j=274
    · subst j
      simp only [hcs,Function.update_same]
      unfold deltaWord
      split_ifs <;> apply hB
    · simpa [hcs,hj] using hB j
  have hclear : clearedStacks c=clearedStacks a := by
    apply clearedStacks_eq
    intro j hj
    have hne : j≠274 := by intro h; subst j; exact hj (by decide)
    simp [hcs,hne]
  obtain ⟨ne,hne,z,he,hzs⟩ := stage_emit_cleanup_eval c
    (by simpa [hcs] using ht) hcl tables width rowWidth positions valid
    (by simpa [hcs] using hv) (by simpa [hcs] using hi)
    (by simpa [hcs] using hn) (by simpa [hcs] using hr)
    (by simpa [hcs] using hp) (by simpa [hcs] using hw)
    (by simpa [hcs] using hrw) B hcb
  have hemit : emitterSize c=emitterSize a := by simp [emitterSize,hcs]
  have hdlen : (deltaWord a).length ≤ B := by
    unfold deltaWord
    split_ifs <;> apply hB
  refine ⟨nc+(7*(deltaWord a).length+6+ne),?_,z,prepend_cleanup hc (prepend_cleanup hd he),?_⟩
  · simp only [hcs,Function.update_same,Function.update_of_ne (by decide : (47:Fin 320)≠274),
      Function.update_of_ne (by decide : (313:Fin 320)≠274),
      Function.update_of_ne (by decide : (314:Fin 320)≠274),hemit] at hne
    unfold finishBound
    omega
  · simpa [hcs,hclear,sourceWord] using hzs

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval_oai
