-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:53:36.81566+00:00
-- url     : https://prove2.me/submissions/8277ce42-0c5a-4a5e-83cd-f80fd2bffda1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval_with_inputLengths
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_time_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem clearPrivate_eq : clearPrivate = BankRoutines.clearCmd 679 (0 : Fin 40) 1
    ((List.finRange 262).map (block 417 262 (by decide))) := rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Frontend output placement leaves the packing destinations untouched. -/
theorem packingSpare_of_frontend_frame (a b : Data) (hs : PackingSpare a)
    (hf : ∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
      (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i) : PackingSpare b := by
  have he (i : Fin 768) (hi : i∈([684,133,135,136] : List (Fin 768))) :
      b.stacks i=a.stacks i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;>
      exact hf _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  refine ⟨(he _ (by simp)).trans hs.1,(he _ (by simp)).trans hs.2.1,
    (he _ (by simp)).trans hs.2.2.1,(he _ (by simp)).trans hs.2.2.2.1,?_⟩
  intro i
  have hi := i.isLt
  have hh : b.stacks (LayoutMasters.high i)=a.stacks (LayoutMasters.high i) := by
    apply hf
    · right; simp [LayoutMasters.high]; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro j h
      have hv := congrArg Fin.val h
      fin_cases j <;> simp [Exports.destination,LayoutMasters.high] at hv <;> omega
  exact hh.trans (hs.2.2.2.2 i)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRegisterSafety
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Structural register frames for the actual frontend syntax. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety
open SubexponentialSAT BitProgram StructuredCalls

theorem base_frame {r s : ℕ} {c : StructuredProgram.Cmd r s} {n : ℕ}
    {a b : State r s} (he : StructuredProgram.Eval c n a b) (j : Fin r)
    (hs : baseSafe j c) : b.regs j=a.regs j := by
  induction he with
  | skip => rfl
  | atom a d => exact hs d
  | seq _ _ ih ih' => exact (ih' hs.2).trans (ih hs.1)
  | ite_true _ _ ih => exact ih hs.1
  | ite_false _ _ ih => exact ih hs.2
  | while_false => rfl
  | while_true _ _ _ ih ih' => exact (ih' hs).trans (ih hs)

theorem trace_frame {r s l : ℕ} (p : Program r s l) (j : Fin r)
    (hs : ∀ q d, (execInstr (p.code q) d).regs j=d.regs j)
    {n : ℕ} {a b : Cfg r s l} (he : Trace p n a b) : b.regs j=a.regs j := by
  induction he with
  | refl => rfl
  | @cons n a b c hab hbc ih =>
    apply ih.trans
    cases hp : a.pc with
    | none => simp [step,hp] at hab
    | some q =>
      have hb : execInstr (p.code q) a=b := by simpa [step,hp] using hab
      exact hb ▸ hs q a

theorem frame {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (he : Eval c n a b) (j : Fin r) (hs : safe j c) : b.regs j=a.regs j := by
  induction he with
  | base he => exact base_frame he j hs
  | call p he => exact trace_frame p j hs he
  | seq _ _ ih ih' => exact (ih' hs.2).trans (ih hs.1)
  | ite_true _ _ ih => exact ih hs.1
  | ite_false _ _ ih => exact ih hs.2
  | while_false => rfl
  | while_true _ _ _ ih ih' => exact (ih' hs).trans (ih hs)

theorem lift_safe {r s l R S : ℕ} (p : Program r s l)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (j : Fin R)
    (hj : ∀ i, j≠reg i) : safe j (.call (ProgramLinking.liftProgram p reg stk)) := by
  intro q d
  dsimp [ProgramLinking.liftProgram]
  cases p.code q <;>
    simp [ProgramLinking.relocateInstr,execInstr,readRegs,hj]

theorem liftCommand_safe {r s R S : ℕ} (c : Cmd r s) (input output : Fin s)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (j : Fin R)
    (hj : ∀ i, j≠reg i) : safe j (liftCommand c input output reg stk) :=
  lift_safe _ _ _ _ hj

theorem copy_safe {r s : ℕ} (src dst tmp : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) : safe j (.call (StackRoutines.copyProgram src dst tmp v p)) := by
  intro q d
  fin_cases q <;> simp [execInstr,readRegs,hv,hp]

theorem clear_safe {r s : ℕ} (src : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) : safe j (.call (StackRoutines.clearProgram src v p)) := by
  intro q d
  fin_cases q <;> simp [execInstr,readRegs,hv,hp]

theorem clearCmd_safe {r s : ℕ} (tmp : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) (xs : List (Fin s)) : safe j (BankRoutines.clearCmd tmp v p xs) := by
  induction xs with
  | nil => exact clear_safe _ _ _ _ hv hp
  | cons x xs ih => exact ⟨clear_safe _ _ _ _ hv hp,ih⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRegisterFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls RegisterSafety
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
attribute [local irreducible] clearPrivate

private theorem outside (j : Fin 40) (hj : 11 ≤ j.val) (n : ℕ) (hn : n ≤ 11)
    (hn' : n ≤ 40) (i : Fin n) : j≠registers n hn' i := by
  intro h
  have := congrArg Fin.val h
  dsimp [registers] at this
  omega

private theorem copies_safe (j : Fin 40) (hj : 11 ≤ j.val)
    (xs : List (Fin 768 × Fin 768)) : safe j (copies xs) := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨copy_safe _ _ _ _ _ _ h0 h1,ih⟩

private theorem clearPrivate_safe (j : Fin 40) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    safe j (BankRoutines.clearCmd 679 (0 : Fin 40) 1
      ((List.finRange 262).map (block 417 262 (by decide)))) :=
  clearCmd_safe 679 0 1 j h0 h1 _

private theorem sequence_safe (j : Fin 40) (xs : List Code)
    (h : ∀ c∈xs, safe j c) : safe j (sequence xs) := by
  induction xs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c List.mem_cons_self,ih (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

private theorem export_safe (j : Fin 40) (hj : 11 ≤ j.val) : safe j Exports.prepareCommand := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  refine ⟨?_,?_,clearCmd_safe _ _ _ _ h0 h1 _⟩
  · apply liftCommand_safe
    intro i h
    have := congrArg Fin.val h
    dsimp [Exports.bankRegs] at this
    omega
  · have hf (f : Exports.Field) : safe j (Exports.fieldCommand f) := by
      unfold Exports.fieldCommand
      split
      · apply liftCommand_safe
        intro i h
        have := congrArg Fin.val h
        dsimp [Exports.regs] at this
        omega
      · exact copy_safe _ _ _ _ _ _ h0 h1
    change safe j (Exports.command Exports.fields)
    generalize Exports.fields=fs
    induction fs with
    | nil => trivial
    | cons f fs ih => exact ⟨hf f,ih⟩

theorem frontend_register_safe (k : ℕ) (j : Fin 40) (hj : 11 ≤ j.val) :
    safe j (frontend k) := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  have hc (s d : Fin 768) : safe j (copy s d) := copy_safe _ _ _ _ _ _ h0 h1
  have hl {n s l : ℕ} (hn : n ≤ 11) (hn' : n ≤ 40) (p : Program n s l)
      (ss : Fin s → Fin 768) : safe j (.call (ProgramLinking.liftProgram p (registers n hn') ss)) :=
    lift_safe p _ ss j (outside j hj n hn hn')
  have hb (s : Fin 768) (w : List Bool) : safe j (loadBits s w) :=
    liftCommand_safe _ _ _ _ _ _ (outside j hj 8 (by decide) (by decide))
  have hne (i : Fin 40) (hi : i.val < 11) : j≠i := by
    intro h; subst j; omega
  have hr : safe j resetScopeRegs := by
    simp only [resetScopeRegs,setRegs,SubexpParameterProgram.atoms,safe,baseSafe]
    simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,
      hne 0 (by decide),hne 1 (by decide),hne 2 (by decide),hne 3 (by decide),hne 4 (by decide),hne 5 (by decide),hne 6 (by decide),hne 7 (by decide),hne 8 (by decide),hne 9 (by decide),hne 10 (by decide)]
  have har : safe j arityRegisters := by
    simp only [arityRegisters,setRegs,SubexpParameterProgram.atoms,safe,baseSafe]
    simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,
hne 7 (by decide),hne 8 (by decide),hne 9 (by decide)]
  have hs (cs : List Code) (h : ∀ c∈cs, safe j c) := sequence_safe j cs h
  have hseq {cs : List Code} (h : ∀ c∈cs, safe j c) : safe j (sequence cs) := hs cs h
  have hbin (s d : Fin 768) : safe j (binary s d) := hl (by decide) _ _ _
  have hcount : safe j countHashes := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl
    · exact hc _ _
    · exact hl (by decide) _ _ _
  have hraw : safe j rawCommand := by
    refine ⟨?_,hl (by decide) _ _ _,hc _ _⟩
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl
    · exact copies_safe j hj _
    · exact hb _ _
    · exact hr
  have hhigh : safe j highCommand := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hc _ _
    · exact hl (by decide) _ _ _
    · exact copies_safe j hj _
    · exact hl (by decide) _ _ _
    · exact hc _ _
    · exact hl (by decide) _ _ _
  have hmeasure : safe j measureCommand := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact copies_safe j hj _
    · exact hl (by decide) _ _ _
    · exact copies_safe j hj _
    · exact har
    · exact hl (by decide) _ _ _
    · exact hl (by decide) _ _ _
  have hnumeric : safe j (numericStage k) := by
    refine ⟨copies_safe j hj _,hb _ _,?_⟩
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> exact hbin _ _
  refine ⟨hcount, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hraw, ?_⟩
    refine ⟨hhigh, ?_⟩
    refine ⟨hmeasure, ?_⟩
    constructor
    · exact hnumeric
    · exact hl (by decide) _ _ _
  · refine ⟨export_safe j hj, ?_⟩
    refine ⟨hl (by decide) _ _ _, ?_⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hc _ _, hl (by decide) _ _ _⟩
    · have heq : clearPrivate = BankRoutines.clearCmd 679 (0 : Fin 40) 1
          ((List.finRange 262).map (block 417 262 (by decide))) := by
        exact clearPrivate_eq
      exact heq.symm ▸ clearPrivate_safe j h0 h1

/-- All parser registers, including 16, 17, and 18, survive the actual native
frontend on both outcomes of its computed guard. -/
theorem frontend_register_frame (k : ℕ) {n : ℕ} {a b : Data}
    (he : Eval (frontend k) n a b) (j : Fin 40) (hj : 11 ≤ j.val) :
    b.regs j=a.regs j := frame he j (frontend_register_safe k j hj)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryFrontState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem front_state_oai (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a) (hs : PackingSpare a) :
    ∃ n b l w,
      Eval (LeafQueryFrontend.frontend k) n a b ∧
      n ≤ q.inputBudget k ∧
      FrontState q k a b l w := by
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,hn,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe,hcanonical⟩ :=
    LeafQueryFrontend.frontend_eval_with_inputLengths q k a hv hr ho
  refine ⟨n,b,l,w,he,LeafQueryFrontend.frontend_time_le q k hv hr ho he,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hframe,?_,h141,hcanonical⟩
  · exact h704
  · exact h718
  · exact h338
  · exact h719
  · exact h134
  · exact hex
  · exact hbank
  · exact hshape
  · exact hguard
  · exact hclean
  · exact packingSpare_of_frontend_frame a b hs hframe
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hr.2.2.2.2.2.2.1
  · exact LeafQueryFrontend.frontend_register_frame k he

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state_oai
