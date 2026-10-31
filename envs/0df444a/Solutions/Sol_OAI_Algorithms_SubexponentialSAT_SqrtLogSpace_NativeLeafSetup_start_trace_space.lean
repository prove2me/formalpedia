-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:54:40.731883+00:00
-- url     : https://prove2.me/submissions/d58c3f05-605b-49b2-8a17-985a588bfd7c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_clauseCount_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_prepareHash_eval

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

theorem saveWidth_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval saveWidth (2*(a.stacks 783).length+7*(a.stacks 768).length+8)
      a (routed (768,783) a) := route_eval (768,783) (by unfold routeValid; decide) a ht

theorem saveWidth_value (a : Data) :
    (routed (768,783) a).stacks 783=a.stacks 768 := by simp [routed]

theorem saveWidth_frame (a : Data) (i : Fin 896) (hi : i≠783) :
    (routed (768,783) a).stacks i=a.stacks i := by simp [routed,hi]

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStart
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed outer-leaf startup: count the actual clause records, compute the
numeric hash parameters, and preserve the exact binary decoder width. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem selector_port_val (j : Fin 14) :
    (LeafProgram.HashParameters.ports.hash.stack j).val=768+j.val := by
  fin_cases j <;> rfl

theorem start_eval (a : Data) (W : ℕ) (records : List (List Bool))
    (hW : WordBound W a) (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i=[])
    (hformula : a.stacks 784=Encoding.encodeList id records) (hm : records≠[]) :
    ∃ t ≤ startBudget W records, ∃ b, Eval start t a b ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
        (BinaryArithmetic.toNat (a.stacks 786)) ∧
      (∀ i : Fin 896, 784 ≤ i.val → b.stacks i=a.stacks i) := by
  let C := LeafProgram.ClauseCount.budget records+1
  obtain ⟨nc,c,hec,hnc,hcm,_,hcf⟩ := clauseCount_eval a records hformula
    (fun i hi => hempty i (by omega)) (hempty 782 (by decide))
  have hcW : WordBound (W+C) c := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hW hec) (by omega)
  have hcr : Execution.HashInputs.Ready (projectState
      LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack c) := by
    intro j _ _ _ _
    change c.stacks (LeafProgram.HashParameters.ports.hash.stack j)=[]
    have hj := selector_port_val j
    rw [hcf _ (by intro h; have hh:=congrArg Fin.val h; have:=j.isLt; omega)]
    exact hempty _ (by have:=j.isLt; omega)
  have hc767 : c.stacks 767=[] := (hcf 767 (by decide)).trans (hempty 767 (by decide))
  have hcm0 : BinaryArithmetic.toNat (c.stacks 782)≠0 := by
    rw [hcm]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hm)
  obtain ⟨nh,hnh,h,heh,hwh,hrh,h0,h5,h6,_,hhf⟩ := prepareHash_eval c (W+C) hcW hcr hcm0 hc767
  let H := prepareHashBudget (W+C)
  have hhW : WordBound (W+C+H) h := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hcW heh) (by omega)
  let b := routed (768,783) h
  have hsave := saveWidth_eval h (hwh 767)
  have hb768 : b.stacks 768=h.stacks 768 := saveWidth_frame h 768 (by decide)
  have bf (i : Fin 896) (hi : 784 ≤ i.val) : b.stacks i=a.stacks i := by
    rw [saveWidth_frame h i (by intro he; have hv:=congrArg Fin.val he; change i.val=783 at hv; omega),hhf i (by omega),hcf i]
    intro he; have hv:=congrArg Fin.val he; change i.val=782 at hv; omega
  have hc785 : c.stacks 785=a.stacks 785 := hcf 785 (by decide)
  have hc786 : c.stacks 786=a.stacks 786 := hcf 786 (by decide)
  refine ⟨nc+(nh+(2*(h.stacks 783).length+7*(h.stacks 768).length+8)),?_,b,
    hec.seq (heh.seq hsave),?_,bf⟩
  · have h783 := hhW 783
    have h768 := hhW 768
    dsimp only [startBudget]
    change nh ≤ H at hnh
    change nc ≤ C at hnc
    dsimp only [C,H] at *
    omega
  · constructor
    · intro i
      rw [saveWidth_frame h (workerStack i) (by
        intro he; have hh:=congrArg Fin.val he
        simp only [workerStack,Fin.val_castAdd] at hh
        have:=i.isLt; omega)]
      exact hwh i
    · intro j h0 h5 h6 h9
      change b.stacks (LeafProgram.HashParameters.ports.hash.stack j)=[]
      rw [saveWidth_frame h _ (by
        intro he; have hh:=congrArg Fin.val he
        have hj:=selector_port_val j; have:=j.isLt; omega)]
      exact hrh j h0 h5 h6 h9
    · rw [bf 785 (by decide)]
    · rw [saveWidth_frame h 782 (by decide),hhf 782 (by decide),hcm]
    · rw [bf 786 (by decide)]
    · rw [hb768,h0,hcm]
    · rw [saveWidth_frame h 773 (by decide),h5,hcm,hc786]
    · rw [saveWidth_frame h 774 (by decide),h6,hc785,hcm]
    · exact (saveWidth_value h).trans hb768.symm

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupOuterCostStartupBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT

theorem record_lengths (records : List (List Bool)) :
    (records.map List.length).sum ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,Encoding.length_encodeList_cons,id_eq]
    omega

theorem count_budget (W : ℕ) (records : List (List Bool))
    (hW : (Encoding.encodeList id records).length ≤ W) :
    LeafProgram.ClauseCount.budget records+1 ≤ 100*(W+1)^2 := by
  have hs := record_lengths records
  have hn := Encoding.length_encodeList_lower id records
  have hc : SubexpScopeCountSetup.countBudget records ≤ 17*W+10 := by
    unfold SubexpScopeCountSetup.countBudget SubexpSunflowerProgram.CountRecords.loopSteps
    omega
  unfold LeafProgram.ClauseCount.budget
  nlinarith

theorem startBudget_bound (W : ℕ) (records : List (List Bool))
    (hW : (Encoding.encodeList id records).length ≤ W) :
    LeafOuterProgram.startBudget W records ≤ startupConstant*(W+1)^4 := by
  have hc := count_budget W records hW
  dsimp only [LeafOuterProgram.startBudget,LeafOuterProgram.prepareHashBudget]
  calc
    _ ≤ 100*(W+1)^2+
        (10000000000*(W+100*(W+1)^2+1)^2+1+
          1536*(W+100*(W+1)^2+(10000000000*(W+100*(W+1)^2+1)^2+1))+2348)+
        9*(W+100*(W+1)^2+
          (10000000000*(W+100*(W+1)^2+1)^2+1+
          1536*(W+100*(W+1)^2+(10000000000*(W+100*(W+1)^2+1)^2+1))+2348))+8 := by
      gcongr
    _ ≤ _ := by unfold startupConstant; ring_nf; omega

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- The runtime clause scan and hash arithmetic establish the physical
startup boundary from the actual encoded formula, including padded inputs. -/
theorem start_trace_space_oai (a : Data) (W : ℕ) (records : List (List Bool))
    (hW : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ []) :
    ∃ steps b, steps ≤ startBudget W records ∧
      steps ≤ CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 ∧
      Eval start steps a b ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
        (BinaryArithmetic.toNat (a.stacks 786)) ∧
      (∀ i : Fin 896, 784 ≤ i.val → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + startBudget W records) ∧
      Trace (compiled start 784 788) (steps + 1)
        (a.withPC (some (compiled start 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled start 784 788) k
        (a.withPC (some (compiled start 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 + 1 := by
  obtain ⟨steps, ht, b, he, hr, hf⟩ := start_eval a W records hW hempty hformula hm
  have hrecords : (Encoding.encodeList id records).length ≤ W := hformula ▸ hW 784
  have hpoly := CodeSetupOuterCost.startBudget_bound W records hrecords
  refine ⟨steps, b, ht, ht.trans hpoly, he, hr, hf, ?_, compiled_halt_trace he 784 788, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW he) (Nat.add_le_add_left ht W)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space_oai
