-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:15:59.36399+00:00
-- url     : https://prove2.me/submissions/e033eb7e-f90f-4219-98c3-d2352e392e6d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Execution_HashParameters_command_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

theorem work_mem (i : Fin 44) : i ∈ work ↔ 17 ≤ i.val ∧ i.val < 39 := by
  simp only [work,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; dsimp [stackMap]; have := j.isLt; omega
  · intro hi; exact ⟨⟨i.val-17,by omega⟩,Fin.ext (by dsimp [stackMap]; omega)⟩

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/

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

theorem clearWorker_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval clearWorker
      (LeafProgram.Cleanup.Wide.budget (projectState id workerStack a)+1)
      a (workerCleared a) := by
  have h := LeafProgram.Cleanup.Wide.lifted id workerStack Function.injective_id
    (Fin.castAdd_injective 768 128) a (projectState id workerStack a) ht
  simpa only [clearWorker,workerCleared,embedState_project id workerStack a
    Function.injective_id (Fin.castAdd_injective 768 128)] using h

theorem clearWorker_stack (a : Data) (i : Fin 768) :
    (workerCleared a).stacks (workerStack i) = [] :=
  embedState_stack id workerStack a LeafProgram.Cleanup.Wide.blank
    (Fin.castAdd_injective 768 128) i

theorem clearWorker_frame (a : Data) (i : Fin 896) (hi : 768 ≤ i.val) :
    (workerCleared a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [workerStack,Fin.val_castAdd] at hv
  omega

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

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact arithmetic preparation, cleanup, and preservation of the decoder's
physical width. The only incoming numerical data are n, m and B. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem hash_stack_val (j : Fin 14) :
    (LeafProgram.HashParameters.ports.hash.stack j).val = 768+j.val := by
  fin_cases j <;> rfl

private theorem parameter_stack_small (j : Fin 44)
    (h14 : j ≠ 14) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (LeafProgram.HashParameters.ports.stack j).val < 782 := by
  fin_cases j <;> simp_all [LeafProgram.HashParameters.ports,LeafProgram.HashParameters.stackMap]

theorem prepareHash_eval_oai (a : Data) (L : ℕ) (hW : WordBound L a)
    (hr : Execution.HashInputs.Ready (projectState
      LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks 782) ≠ 0) (ht : a.stacks 767=[]) :
    ∃ t ≤ prepareHashBudget L, ∃ b,
      Eval prepareHash t a b ∧ WorkerEmpty b ∧
      Execution.HashInputs.Ready (projectState
        LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks 768)=3*BinaryArithmetic.toNat (a.stacks 782) ∧
      BinaryArithmetic.toNat (b.stacks 773)=SparseCode.distanceDenom
        (BinaryArithmetic.toNat (a.stacks 782)) (BinaryArithmetic.toNat (a.stacks 786)) ∧
      BinaryArithmetic.toNat (b.stacks 774)=HashSelect.loopCap
        (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782)) ∧
      b.stacks 777=a.stacks 777 ∧
      (∀ i : Fin 896, 782 ≤ i.val → b.stacks i=a.stacks i) := by
  let p := LeafProgram.HashParameters.ports
  obtain ⟨t,htb,c,he,hready,h0,h5,h6,h9,hf,hout,_⟩ :=
    Execution.HashParameters.command_eval p a L (fun i => hW (p.stack i)) hr hm
  have hc767 : c.stacks 767=[] := (hout 767 (by decide)).trans ht
  have hcW : WordBound (L+(10000000000*(L+1)^2+1)) c :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hW he) (by omega)
  have hclean := clearWorker_eval c hc767
  have hcost := cleanup_budget_le c _ hcW
  have cf (i : Fin 896) (hi : 782 ≤ i.val) : c.stacks i=a.stacks i := by
    by_cases hj : ∃ j, p.stack j=i
    · obtain ⟨j,rfl⟩ := hj
      have cases : j=14 ∨ j=15 ∨ j=16 := by
        by_contra hn
        push Not at hn
        have hh := parameter_stack_small j hn.1 hn.2.1 hn.2.2
        change (p.stack j).val < 782 at hh
        omega
      rcases cases with rfl|rfl|rfl
      all_goals apply hf <;> first | (rw [HashParametersProgram.ABI.work_mem]; decide) | decide
    · exact hout i (by intro j h; exact hj ⟨j,h⟩)
  refine ⟨_,?_,workerCleared c,he.seq hclean,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp only [prepareHashBudget]; omega
  · exact clearWorker_stack c
  · intro j hj0 hj5 hj6 hj9
    change (workerCleared c).stacks (p.hash.stack j)=[]
    rw [clearWorker_frame c _ (by have hv : (p.hash.stack j).val=768+j.val := hash_stack_val j; omega)]
    exact hready j hj0 hj5 hj6 hj9
  · rw [clearWorker_frame c 768 (by decide)]; exact h0
  · rw [clearWorker_frame c 773 (by decide)]; exact h5
  · rw [clearWorker_frame c 774 (by decide)]; exact h6
  · rw [clearWorker_frame c 777 (by decide)]; exact h9
  · intro i hi
    exact (clearWorker_frame c i (by omega)).trans (cf i hi)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval_oai
