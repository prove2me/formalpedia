-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:24:43.096+00:00
-- url     : https://prove2.me/submissions/5a97a06a-006d-4e6f-9190-2aeaacb470b5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_dispatch_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem program_runsIn (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) (hvalid : hasMarked=true → m < clauses.length) :
    ∃ rf, rf 5=decide (f < rows.length) ∧ rf 6=(hasMarked && decide (f=rows.length)) ∧
      rf 7=hasMarked ∧
      RunsIn program (budget rows clauses m f)
        ((input regs rows clauses hasMarked m f).withPC (some program.entry))
        ((⟨rf,outputStacks rows clauses hasMarked m f⟩ : Data).withPC none) := by
  let d := input regs rows clauses hasMarked m f
  let a := afterTransfer d 2 6 0 1
  have hp : Eval prepare (3*f+6) d a := by
    dsimp [a]
    simpa [prepare,d,input,baseStacks,Nat.mul_add,Nat.add_assoc] using
      transfer_eval d 2 6 0 1 (by decide) (by decide)
  obtain ⟨n,e,hn,he,hs,h5,h6,h7⟩ := dispatch_eval a rows clauses hasMarked m f
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,input,readRegs]) hvalid
    (by intro j hj; fin_cases j <;> simp_all [a,d,afterTransfer,
      StackRoutines.transferStacks,input,baseStacks])
    (by simp [TestClean,a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
  have hout : e.stacks=outputStacks rows clauses hasMarked m f := by
    rw [hs]
    funext j
    fin_cases j <;> simp [finishedStacks,a,d,afterTransfer,StackRoutines.transferStacks,
      input,baseStacks,outputStacks]
  have heq : e=(⟨e.regs,outputStacks rows clauses hasMarked m f⟩ : Data) := by
    exact state_ext rfl hout
  refine ⟨e.regs,h5,h6,?_,3*f+6+n+1,?_,?_⟩
  · simpa [a,d,afterTransfer,input,readRegs] using h7
  · unfold budget; omega
  · have ht := compiled_halt_trace (hp.seq he) 2 15
    rw [heq] at ht
    exact ht

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem register_injective : Function.Injective register := Fin.castAdd_injective 8 32
theorem stackMap_injective : Function.Injective stackMap := by decide

theorem stage_eval (a : Data) (hwork : a.stacks 359=[]) :
    Eval (.seq copyID readFlag) (7*(a.stacks 149).length+6) a (staged a) := by
  have hc := copy_eval a 149 152 359 0 1
    (by decide) (by decide) (by decide) (by decide) hwork
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0) (copied a))
  have he : (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0).eval
      (copied a)=staged a := by
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  rw [he] at hp
  convert hc.seq hp using 1
  all_goals try with_reducible_and_instances rfl

theorem command_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark)
    (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hwork : ∀ i∈scratch, a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length) :
    ∃ k rf, k ≤ 7*(a.stacks 149).length+6+
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval command k a (finished a rf rows clauses marked mark factor) ∧
      rf 5=decide (factor < rows.length) ∧
      rf 6=(marked && decide (factor=rows.length)) ∧ rf 7=marked := by
  obtain ⟨rf,h5,h6,h7,k,hk,he⟩ := LeafFactorDispatchProgram.program_runsIn
    ((staged a).regs ∘ register) rows clauses marked mark factor hvalid
  have hi : projectState register stackMap (staged a)=
      LeafFactorDispatchProgram.input ((staged a).regs ∘ register)
        rows clauses marked mark factor := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;>
        simp [staged,register,readRegs,hflag]
    · funext i
      fin_cases i <;>
        simp_all [stackMap,LeafFactorDispatchProgram.input,
          LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,
          staged,copied,afterCopy,StackRoutines.copyStacks,scratch]
  rw [← hi] at he
  have hd := eval_call_from_state LeafFactorDispatchProgram.program register stackMap
    (staged a) register_injective stackMap_injective he
  have hs := stage_eval a (hwork 359 (by simp [scratch]))
  exact ⟨_,rf,by omega,hs.seq hd,h5,h6,h7⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatchFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte-store frame for the paid factor dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf rows clauses marked mark factor).stacks =
      Function.update a.stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf rows clauses marked mark factor).stacks (stackMap j) =
        LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor j from
      embedState_stack register stackMap (staged a) _ stackMap_injective j]
    fin_cases j <;>
      simp_all [stackMap,LeafFactorDispatchProgram.outputStacks,
        LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,scratch]
  · have h152 : i ≠ 152 := by intro h; subst i; exact hin ⟨2,rfl⟩
    have h154 : i ≠ 154 := by intro h; subst i; exact hin ⟨15,rfl⟩
    rw [show (finished a rf rows clauses marked mark factor).stacks i = (staged a).stacks i from
      embedState_stack_frame register stackMap (staged a) _ i hin]
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,h152,h154]

theorem finished_role_hash (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).regs 5 = rf 5 :=
  embedState_register register stackMap (staged a) _ register_injective 5

theorem finished_role_marked (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).regs 6 = rf 6 :=
  embedState_register register stackMap (staged a) _ register_injective 6

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem clear_eval (a : Data) (src : Fin 896) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 a.regs a.stacks)

theorem clearCallback_eval (a : Data) :
    Eval clearCallback (clearCallbackCost a) a (callbackInitial a) :=
  eval_liftCommand_from_state clearCallbackLocal 149 149 localRegister lowStack a
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (clearMany_eval callbackScratch (projectState localRegister lowStack a))

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

theorem callbackInitial_frame (a : Data) (i : Fin 896)
    (hi : i ∉ callbackScratch.map lowStack) :
    (callbackInitial a).stacks i = a.stacks i := by
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ callbackScratch := by
      intro hm
      exact hi (List.mem_map.mpr ⟨j, hm, hj⟩)
    rw [← hj, callbackInitial_low, ite_eq_right hn]
  · apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

theorem returnToRecords_eval (a : Data) : Eval returnToRecords 3 a (returned a) := by
  let b : Data := ⟨Function.update a.regs 13 false, a.stacks⟩
  let c : Data := ⟨Function.update b.regs 14 true, a.stacks⟩
  have h1 : Eval (.base (.atom (.set 13 false))) 1 a b := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 14 true))) 1 b c := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.set 15 false))) 1 c (returned a) := .base (.atom _ _)
  exact h1.seq (h2.seq h3)

theorem callbackFinish_eval (a : Data) :
    Eval (.seq (clear 149) returnToRecords) (2 * (a.stacks 149).length + 6)
      a (callbackFinished a) := by
  convert (clear_eval a 149).seq (returnToRecords_eval (cleared a 149)) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

/-- Neutral IDs execute the dispatcher and record cleanup, retaining the
running product. No incidence lookup or arithmetic branch is executed. -/
theorem callback_neutral_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length)
    (hhash : ¬factor < rows.length)
    (hmarked : (marked && decide (factor = rows.length)) = false) :
    ∃ steps b, steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval callback steps a b ∧
      b.stacks = Function.update (callbackInitial a).stacks 149 [] ∧
      b.regs 13 = false ∧ b.regs 14 = true ∧ b.regs 15 = false := by
  let c := callbackInitial a
  let low := projectState id lowStack c
  have frame (i : Fin 768) (hi : i ∉ callbackScratch) : low.stacks i = a.stacks (lowStack i) := by
    exact (callbackInitial_low a i).trans (ite_eq_right hi)
  have hr : low.stacks 701 = Encoding.encodeList id rows := (frame 701 (by decide)).trans hrows
  have hc : low.stacks 700 = Encoding.encodeList id clauses := (frame 700 (by decide)).trans hclauses
  have hn : low.stacks 704 = List.replicate rows.length true := (frame 704 (by decide)).trans hcount
  have hm : low.stacks 705 = Encoding.encodeNat mark := (frame 705 (by decide)).trans hmark
  have hf : low.stacks 706 = [marked] := (frame 706 (by decide)).trans hflag
  have hid : low.stacks 149 = (Encoding.encodeNat factor).reverse := (frame 149 (by decide)).trans hfactor
  have hwork : ∀ i ∈ FactorDispatch.scratch, low.stacks i = [] := by
    intro i hi
    have hmem : i ∈ callbackScratch := by
      simp only [callbackScratch, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hi))
    exact (callbackInitial_low a i).trans (ite_eq_left hmem)
  obtain ⟨kd, rd, hkd, hd, h5, h6, h7⟩ :=
    FactorDispatch.command_eval low rows clauses marked mark factor hr hc hn hm hf hid hwork hvalid
  let out := FactorDispatch.finished low rd rows clauses marked mark factor
  let wide := embedState id lowStack c out
  have hdispatch : Eval (liftLow FactorDispatch.command 149 154) (kd + 1) c wide :=
    eval_liftCommand_from_state FactorDispatch.command 149 154 id lowStack c
      Function.injective_id (Fin.castAdd_injective _ _) hd
  have hwide5 : wide.regs 5 = false := by
    rw [show wide.regs 5 = out.regs 5 from
      embedState_register id lowStack c out Function.injective_id 5]
    rw [FactorDispatch.finished_role_hash, h5]
    exact decide_eq_false hhash
  have hwide6 : wide.regs 6 = false := by
    rw [show wide.regs 6 = out.regs 6 from
      embedState_register id lowStack c out Function.injective_id 6]
    rw [FactorDispatch.finished_role_marked, h6, hmarked]
  have hpayload : LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor = [] := by
    simp [LeafFactorDispatchProgram.selectedPayload, hhash, hmarked]
  have hlow : out.stacks = low.stacks := by
    rw [FactorDispatch.finished_stacks low rd rows clauses marked mark factor hr hc hn hm hwork,
      hpayload]
    exact Function.update_eq_self_iff.mpr (hwork 154 (by decide)).symm
  have hwide : wide.stacks = c.stacks := by
    funext i
    by_cases hi : i.val < 768
    · let j : Fin 768 := ⟨i.val, hi⟩
      have hj : lowStack j = i := Fin.ext rfl
      rw [← hj, embedState_stack id lowStack c out (Fin.castAdd_injective _ _) j, hlow]
      rfl
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega
  have hchoose : Eval choose 2 wide wide :=
    Eval.ite_false hwide5 (Eval.ite_false hwide6 (Eval.base (StructuredProgram.Eval.skip wide)))
  refine ⟨clearCallbackCost a + ((kd + 1) + (2 + (2 * (wide.stacks 149).length + 6))),
    callbackFinished wide, ?_, (clearCallback_eval a).seq (hdispatch.seq
      (hchoose.seq (callbackFinish_eval wide))), ?_, ?_, ?_, ?_⟩
  · have h149 : wide.stacks 149 = a.stacks 149 := by
      rw [hwide]
      exact callbackInitial_frame a 149 (by decide)
    have hl149 : low.stacks 149 = a.stacks 149 := frame 149 (by decide)
    rw [h149]
    rw [hl149] at hkd
    omega
  · exact congrArg (fun (store : Fin 896 → List Bool) => Function.update store 149 []) hwide
  all_goals simp [callbackFinished, returned]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The paid clear preserves an already established callback boundary. -/
theorem callbackInitial_stacks (a : FactorAssignmentProgram.Data)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    (callbackInitial a).stacks = a.stacks := by
  funext i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj, hclean j hj]
  · exact callbackInitial_frame a i hi

/-- A neutral ID leaves the actual accumulated dictionary unchanged and
restores the same callback boundary, after its paid dispatch and return. -/
theorem callback_neutral_frame (a : FactorAssignmentProgram.Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length)
    (hhash : ¬factor < rows.length)
    (hmarked : (marked && decide (factor = rows.length)) = false)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    ∃ steps b, steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval callback steps a b ∧ b.stacks = Function.update a.stacks 149 [] ∧
      b.regs 13 = false ∧ b.regs 14 = true ∧ b.regs 15 = false := by
  obtain ⟨steps, b, hs, he, hb, h13, h14, h15⟩ :=
    callback_neutral_eval a rows clauses marked mark factor hrows hclauses hcount hmark
      hflag hfactor hvalid hhash hmarked
  exact ⟨steps, b, hs, he, hb.trans
    (congrArg (fun ss : Fin 896 → List Bool => Function.update ss 149 [])
      (callbackInitial_stacks a hclean)), h13, h14, h15⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

/-- Neutral original IDs execute their paid record path and preserve the
complete accumulated dictionary. -/
theorem neutral_callback_eval_oai (h : Input q A S one seed a f)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hh : ¬ f < q.rows.length)
    (hm : (q.marked && decide (f = q.rows.length)) = false) :
    ∃ steps z,
      NativeSemantics.Good ∅ q.u q.J seed ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes seed) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨steps,z,hs,he,hz,h13,h14,h15⟩ := callback_neutral_frame a q.rawRows q.clauses
    q.marked q.mark f h.rows h.clauses h.count h.mark h.flag h.factor hvalid
    (by simpa only [Factor.Spec.rawRows, List.length_map] using hh)
    (by simpa only [Factor.Spec.rawRows, List.length_map] using hm) h.blank
  refine ⟨steps,z,hseed,hs,he,?_,h13,h14,h15⟩
  rw [hz]
  symm
  apply Function.update_eq_self_iff.mpr
  simpa only [Function.update_of_ne (show (151 : Fin 896) ≠ 149 by decide)] using h.seedBytes.symm

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval_oai
