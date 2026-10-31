-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:43:24.296963+00:00
-- url     : https://prove2.me/submissions/a693554e-ad38-447b-b2ce-9d65e1d7a1af

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassAdapter_mass_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafOuterNative_stageTrial_eval

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

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

theorem trialStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h2 : i≠702) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (trialStaged a).stacks i=a.stacks i :=
  (prefixed_frame _ i h1 h2).trans (finalStaged_frame a i h0 h1 h7 h8 h9)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

theorem cleanup_eval (a : State 40 896) (ht : a.stacks 767 = []) :
    Eval cleanup (cleanupCost a) a (cleaned a) := by
  simpa only [cleanup, cleanupCost, cleaned, stagedPorts, List.length_cons, List.length_nil] using
    BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 stagedPorts (by decide) a.regs a.stacks ht

theorem staged_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ stagedPorts) :
    (LeafOuterNative.trialStaged a).stacks i = a.stacks i := by
  have hne : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [stagedPorts] using hi
  exact LeafOuterNative.trialStaged_frame a i hne.1 hne.2.1 hne.2.2.1
    hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

/-- The inner mass collector sees the physically staged sources. After all
marked counts have been added, actual cleanup restores every source master. -/
theorem eval_oai (query : Cmd 40 896) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : State 40 896) (m : ℕ)
    (ha : ReferencesReady a) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hcollector : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hempty : ∀ i ∈ stagedPorts, a.stacks i = [])
    (hvalid : ∀ e : Fin m, valid (Encoding.encodeNat e.val))
    (hq : ∀ bits tail (base : State 40 896), valid bits →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged a)) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged a) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ n ≤ budget a queryCost width m, ∃ b, Eval (command query) n a b ∧
      b.stacks = Function.update a.stacks 769
        (DisjointReuse.binaryNat (((RowSelectionProgram.Index.alphabet m).map count).sum)) := by
  let s := LeafOuterNative.trialStaged a
  have hs : ReferencesReady s := by
    constructor
    · rw [staged_frame a 767 (by decide)]
      exact ha.scratch
    · intro i hi
      have hne : i ∉ stagedPorts := by
        simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at *
        rcases hi with hi | rfl
        · intro hh
          rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
        · decide
      rw [staged_frame a i hne]
      exact ha.empty i hi
  obtain ⟨nc, hnc, c, hc, hout⟩ := mass_eval query count queryCost width valid s m hs
    (by rw [staged_frame a 782 (by decide)]; exact hm)
    (by rw [staged_frame a 321 (by decide)]; exact hcollector 321 (by decide) (by decide))
    (by rw [staged_frame a 322 (by decide)]; exact hcollector 322 (by decide) (by decide))
    (by rw [staged_frame a 323 (by decide)]; exact hcollector 323 (by decide) (by decide))
    (by rw [staged_frame a 324 (by decide)]; exact hcollector 324 (by decide) (by decide)) hvalid hq
  have hc767 : c.stacks 767 = [] := by simp [hout, hs.scratch]
  have hcost : cleanupCost c = cleanupCost s := by
    unfold cleanupCost
    congr 2
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ 769 := by
      simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp [hout, hne]
  have hbudget : massBudget s queryCost width m = massBudget a queryCost width m := by
    simp only [s, massBudget, routeCost, staged_frame a 0 (by decide),
      staged_frame a 782 (by decide), staged_frame a 769 (by decide)]
  refine ⟨LeafOuterNative.stageTrialCost a + (nc + cleanupCost c), ?_, cleaned c,
    (LeafOuterNative.stageTrial_eval a ha.scratch).seq (hc.seq (cleanup_eval c hc767)), ?_⟩
  · rw [hcost]
    rw [hbudget] at hnc
    change LeafOuterNative.stageTrialCost a + (nc + cleanupCost s) ≤
      LeafOuterNative.stageTrialCost a + cleanupCost s + massBudget a queryCost width m
    omega
  funext i
  by_cases hi : i ∈ stagedPorts
  · have hne : i ≠ 769 := by
      simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp [cleaned, BankRoutines.clearBankStacks, hi, hne, hempty i hi]
  · simp only [cleaned, BankRoutines.clearBankStacks, ite_eq_right hi, hout]
    by_cases h769 : i = 769
    · subst i; simp
    · simp only [Function.update_of_ne h769]
      exact staged_frame a i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.eval_oai
