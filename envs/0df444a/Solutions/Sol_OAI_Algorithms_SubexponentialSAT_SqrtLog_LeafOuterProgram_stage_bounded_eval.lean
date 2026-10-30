-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:56:25.001245+00:00
-- url     : https://prove2.me/submissions/3d8ea357-b7bd-4603-9f48-98e6b0aaa14f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S106

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid restoration of the isolated count-query worker. The selector's mass
contract requires literal frame preservation, so all 340 worker stacks and all
22 registers are restored by actual instructions after exporting the score. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem reset_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (reset is) is.length a (resetState is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip a)
  | cons i is ih =>
      simpa only [reset,resetState,List.length_cons,Nat.add_comm] using
        (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
          (ih ((StructuredProgram.Atom.set i false).eval a))

theorem reset_stacks {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    (resetState is a).stacks = a.stacks := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => exact ih _

theorem reset_regs {r s : ℕ} (is : List (Fin r)) (a : State r s) (i : Fin r) :
    (resetState is a).regs i = if i ∈ is then false else a.regs i := by
  induction is generalizing a with
  | nil => simp [resetState]
  | cons j is ih =>
      rw [resetState,ih]
      by_cases hj : i = j <;> by_cases hi : i ∈ is <;>
        simp [hj,hi,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr]

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanupWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full cleanup for the wider leaf worker including setup pockets. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (a : Data) (htmp : a.stacks 767 = []) :
    Eval command (budget a) a blank := by
  have hc := BankRoutines.clear_eval (767 : Fin 768) (0 : Fin 40) 1 (List.finRange 768)
    (List.nodup_finRange 768) a.regs a.stacks htmp
  let middle : Data := ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks (List.finRange 768) a.stacks⟩
  have hr := reset_eval (List.finRange 40) middle
  have he : resetState (List.finRange 40) middle = blank := by
    cases hs : resetState (List.finRange 40) middle with
    | mk regs stk =>
      have hhregs : regs = fun _ => false := by
        funext i
        have h := reset_regs (List.finRange 40) middle i
        simpa [hs] using h
      have hhstacks : stk = fun _ => [] := by
        have h := reset_stacks (List.finRange 40) middle
        rw [hs] at h
        change stk = _ at h
        rw [h]
        funext i
        simp [middle,BankRoutines.clearBankStacks]
      simp only [hhregs,hhstacks]
      rfl
  rw [he] at hr
  simpa only [command,budget,bytes,List.length_finRange] using hc.seq hr

theorem lifted {r s : ℕ} (register : Fin 40 → Fin r) (stack : Fin 768 → Fin s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (frame : State r s) (a : Data) (htmp : a.stacks 767 = []) :
    Eval (.call (ProgramLinking.liftProgram program register stack)) (budget a+1)
      (embedState register stack frame a) (embedState register stack frame blank) :=
  eval_call_lifted program register stack frame hr hs
    (compiled_halt_trace (command_eval a htmp) 0 0)

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

theorem routes_eval (ps : List Route) (hp : ∀ p ∈ ps, routeValid p)
    (a : Data) (ht : a.stacks 767 = []) :
    Eval (routes ps) (routesCost ps a) a (routesState ps a) := by
  induction ps generalizing a with
  | nil =>
    have h := BankRoutines.clear_call_eval (767 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
    simpa only [routes,routesCost,routesState,ht,List.length_nil,Nat.mul_zero,
      Nat.zero_add,BankRoutines.clearStacks_eq_self_of_empty _ _ ht] using h
  | cons p ps ih =>
    have h := hp p (by simp)
    have htmp : (routed p a).stacks 767 = [] := by
      simpa only [routed,Function.update_of_ne (Ne.symm h.2.2)] using ht
    exact (route_eval p h a ht).seq (ih (fun q hq => hp q (by simp [hq])) (routed p a) htmp)

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

theorem routes_cost_bound (ps : List Route) (a : Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    routesCost ps a ≤ ps.length*(9*B+8)+3 := by
  induction ps generalizing a with
  | nil => simp [routesCost]
  | cons p ps ih =>
    have hb' : ∀ i, ((routed p a).stacks i).length ≤ B := by
      intro i
      by_cases h : i=p.2
      · subst i; simpa [routed] using hb p.1
      · simpa [routed,h] using hb i
    have hh := ih (routed p a) hb'
    have h1 := hb p.1
    have h2 := hb p.2
    simp only [routesCost,routeCost,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem clearWorker_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval clearWorker
      (LeafProgram.Cleanup.Wide.budget (projectState id workerStack a)+1)
      a (workerCleared a) := by
  have h := LeafProgram.Cleanup.Wide.lifted id workerStack Function.injective_id
    (Fin.castAdd_injective 768 128) a (projectState id workerStack a) ht
  simpa only [clearWorker,workerCleared,embedState_project id workerStack a
    Function.injective_id (Fin.castAdd_injective 768 128)] using h

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupBoundSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured bounds for composition of the concrete setup phases

The predicates below retain actual executions. Polynomial coefficients and
degrees are chosen before the input size and the incoming machine state.
-/

namespace SubexponentialSAT.SubexpSetupBoundSpec

open BitProgram StructuredCalls SubexpSetupStorage Filter

theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (ha : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (ha i).trans hBC

/-- A fixed stack gains at most one bit per actual instruction. -/
theorem eval_wordBound {r s B t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) : WordBound (B + t) b := by
  intro i
  have hg := BitProgram.trace_selectedStackBits (compiled cmd i i) {i}
    (compiled_trace he i i)
  have hi : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [BitProgram.selectedStackBits, Finset.sum_singleton,
      StructuredProgram.State.withPC] using hg
  exact hi.trans (Nat.add_le_add_right (ha i) t)

end SubexponentialSAT.SubexpSetupBoundSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact composition and memory charging for fixed outer-leaf stages. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

theorem routes_wordBound (ps : List Route) (a : Data) (B : ℕ) (hb : WordBound B a) :
    WordBound B (routesState ps a) := by
  induction ps generalizing a with
  | nil => exact hb
  | cons p ps ih =>
    apply ih
    intro i
    by_cases hi : i=p.2
    · subst i; simpa [routed] using hb p.1
    · simpa [routed,hi] using hb i

theorem cleanup_budget_le (a : Data) (B : ℕ) (hb : WordBound B a) :
    LeafProgram.Cleanup.Wide.budget (projectState id workerStack a)+1 ≤ 1536*B+2348 := by
  have hsum : ((List.finRange 768).map (fun i => (a.stacks (workerStack i)).length)).sum ≤
      (List.finRange 768).length*B := by
    induction List.finRange 768 with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      have hi := hb (workerStack i)
      omega
  simp only [List.length_finRange] at hsum
  change 2*((List.finRange 768).map (fun i => (a.stacks (workerStack i)).length)).sum+2347+1 ≤ _
  omega

theorem stage_eval {r s l : ℕ} (inputs outputs : List Route)
    (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hwork : ∀ i, stack i ≠ 767)
    (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
    (a : Data) (ht : a.stacks 767 = []) (out : State r s) (budget : ℕ)
    (run : RunsIn p budget
      ((projectState register stack (routesState inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    ∃ n ≤ stageBudget inputs outputs register stack a out budget,
      Eval (stage inputs p register stack outputs) n a
        (stageResult inputs outputs register stack a out) := by
  have he1 := routes_eval inputs hi a ht
  have ht1 : (routesState inputs a).stacks 767 = [] :=
    (routes_frame inputs a 767 (fun q hq => (hi q hq).2.2)).trans ht
  obtain ⟨n,hn,he⟩ := run
  have he2 := eval_call_from_state p register stack (routesState inputs a) hr hs he
  have ht2 : (stageReturned inputs register stack a out).stacks 767 = [] := by
    exact (embedState_stack_frame register stack (routesState inputs a) out 767
      (by rintro ⟨i,h⟩; exact hwork i h)).trans ht1
  have he3 := routes_eval outputs ho (stageReturned inputs register stack a out) ht2
  have ht3 : (stageSaved inputs outputs register stack a out).stacks 767 = [] :=
    (routes_frame outputs (stageReturned inputs register stack a out) 767
      (fun q hq => (ho q hq).2.2)).trans ht2
  have he4 := clearWorker_eval (stageSaved inputs outputs register stack a out) ht3
  refine ⟨_,?_,he1.seq (he2.seq (he3.seq he4))⟩
  dsimp only [stageBudget]
  omega

/-- Uniform linear overhead, including dirty subprogram output cleanup.
The native subprogram's own trace budget is the only non-storage term. -/
theorem stage_bounded_eval_oai {r s l : ℕ} (inputs outputs : List Route)
    (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hwork : ∀ i, stack i ≠ 767)
    (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
    (hli : inputs.length ≤ 32) (hlo : outputs.length ≤ 32)
    (a : Data) (B : ℕ) (hb : WordBound B a) (ht : a.stacks 767 = [])
    (out : State r s) (budget : ℕ)
    (run : RunsIn p budget
      ((projectState register stack (routesState inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    ∃ n ≤ 10000*(B+budget+1),
      Eval (stage inputs p register stack outputs) n a
        (stageResult inputs outputs register stack a out) := by
  have hw1 := routes_wordBound inputs a B hb
  obtain ⟨n,hn,he⟩ := run
  have hcall := eval_call_from_state p register stack (routesState inputs a) hr hs he
  have hw2 : WordBound (B+budget) (stageReturned inputs register stack a out) :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hw1 hcall)
      (Nat.add_le_add_left hn B)
  have hw3 := routes_wordBound outputs (stageReturned inputs register stack a out) (B+budget) hw2
  have hic := routes_cost_bound inputs a B hb
  have hoc := routes_cost_bound outputs (stageReturned inputs register stack a out) (B+budget) hw2
  have hcleanup := cleanup_budget_le (stageSaved inputs outputs register stack a out) (B+budget) hw3
  obtain ⟨steps,hsteps,hrun⟩ := stage_eval inputs outputs p register stack hr hs hwork hi ho
    a ht out budget ⟨n,hn,he⟩
  refine ⟨steps,?_,hrun⟩
  have hi32 := Nat.mul_le_mul_right (9*B+8) hli
  have ho32 := Nat.mul_le_mul_right (9*(B+budget)+8) hlo
  dsimp only [stageBudget] at hsteps
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval_oai
