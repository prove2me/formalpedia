-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:24:49.439984+00:00
-- url     : https://prove2.me/submissions/147e2916-a86c-4c86-8c2b-536125c29e3a

import Mathlib
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S169
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryAdapter_NativeOverlay_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every correctly sized pair of branch streams is accepted by the actual
merge program, and the resulting original-coordinate assignment is unique. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem merge_spec (mask high low : List Bool)
    (hh : high.length = highCount mask)
    (hs : high.length + low.length = mask.length) :
    (merge mask high low).length = mask.length ∧
    selected true mask (merge mask high low) = high ∧
    selected false mask (merge mask high low) = low := by
  induction mask generalizing high low with
  | nil =>
      have hhigh : high = [] := List.eq_nil_of_length_eq_zero (by simpa [highCount, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful] using hh)
      have hlow : low = [] := List.eq_nil_of_length_eq_zero (by simpa [hhigh] using hs)
      simp [hhigh, hlow, merge, selected]
  | cons b mask ih =>
      cases b with
      | false =>
          have hh' : high.length = highCount mask := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases low with
          | nil =>
              have hb : highCount mask ≤ mask.length := by
                exact List.length_filter_le _ _
              simp only [List.length_nil, List.length_cons] at hs
              omega
          | cons x low =>
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh' hs'
              simp [merge, selected, hlen, hhigh, hlow]
      | true =>
          have hh' : high.length = highCount mask + 1 := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases high with
          | nil => simp at hh'
          | cons x high =>
              have hh'' : high.length = highCount mask := by simpa using hh'
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh'' hs'
              simp [merge, selected, hlen, hhigh, hlow]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original-coordinate high-value vector. The existing merger reads
false from its empty low stream, so no high-ID producer or zero-padding oracle
is required. It consumes the mask and high bits and emits the reversed vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem merge_zero_pad (mask high : List Bool) (l : ℕ) :
    merge mask high (List.replicate l false) = zeroMerge mask high := by
  induction mask generalizing high l with
  | nil => rfl
  | cons b mask ih =>
      cases b
      · cases l <;> simp [zeroMerge, merge, ih, List.replicate_succ]
      · simp [zeroMerge, merge, ih]

/-- The emitted vector has exactly the supplied high bits and zero on every
free coordinate. It retains the full original length. -/
theorem zeroMerge_spec (mask high : List Bool) (hh : high.length = highCount mask) :
    (zeroMerge mask high).length = mask.length ∧
    selected true mask (zeroMerge mask high) = high ∧
    selected false mask (zeroMerge mask high) =
      List.replicate (mask.length - highCount mask) false := by
  have hc : highCount mask ≤ mask.length := List.length_filter_le _ _
  have hs : high.length + (List.replicate (mask.length - highCount mask) false).length =
      mask.length := by simp only [List.length_replicate]; omega
  have h := merge_spec mask high (List.replicate (mask.length - highCount mask) false) hh hs
  simpa only [merge_zero_pad] using h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem result_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  by_cases hn : ∃ j, stackMap j=i
  · obtain ⟨j,rfl⟩ := hn
    rw [show (result a rf).stacks (stackMap j)=
      (Overlay.state rf (a.stacks 859) (a.stacks 670)
        (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
          (a.stacks 670) (a.stacks 869)) []).stacks j from
      embedState_stack regMap stackMap a _ (by decide) j]
    fin_cases j <;> simp_all [stackMap,changed,Overlay.state]
  · exact embedState_stack_frame regMap stackMap a _ i hn

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (875 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (875 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 875 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (StackRoutines.clearStacks 875 a.stacks) =
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i ∈ changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 875 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=7 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi



/-- Every raw head candidate is expanded in ambient order and overlaid onto
the retained tuple/high baseline by an actual bounded-memory routine. -/
theorem prepare_trace_space (a : Data) (bound : ℕ)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ rf, Trace prepareProgram steps (a.withPC (some prepareProgram.entry))
      ((result (resetState a) rf).withPC none) ∧ steps≤70*bound+70 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace prepareProgram prefixSteps (a.withPC (some prepareProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤966*bound+70 := by
  have hbits : (resetState a).stacks 859=a.stacks 859 := reset_frame a 859 (by decide)
  have hmask : (resetState a).stacks 670=a.stacks 670 := reset_frame a 670 (by decide)
  have hbase : (resetState a).stacks 869=a.stacks 869 := reset_frame a 869 (by decide)
  obtain ⟨rf,hs⟩ := command_eval (resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i changed a.stacks hi)
    (by simpa only [hbits,hmask] using hh) (by simpa only [hmask,hbase] using hm)
  have hsum : (changed.map (fun i => ((clearStacks 875 a.stacks) i).length)).sum≤7*bound := by
    apply (List.sum_le_card_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=875
      · subst i
        simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have hc : resetCost a≤16*bound+27 := by
    dsimp [resetCost]
    have := hb 875
    omega
  have htime : resetCost a+(7*((resetState a).stacks 859).length+
      47*((resetState a).stacks 670).length+42)+1≤70*bound+70 := by
    rw [hbits,hmask]
    have := hb 859
    have := hb 670
    omega
  have hx := (reset_eval a).seq hs
  refine ⟨_,rf,compiled_halt_trace hx 859 145,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareProgram.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hbound := StructuredSpace.local_stack_bound prepareProgram (steps:=70*bound+70) hin
    prefixSteps intermediate (Nat.le_trans hle htime) htrace i
  omega

@[simp] theorem prepared_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result (resetState a) rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) := by
  rw [result_assignment,reset_frame a 670 (by decide),reset_frame a 859 (by decide),
    reset_frame a 869 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

theorem prepared_scratch (a : Data) (rf : Fin 8 → Bool) (i : Fin 896)
    (hi : i∈([872,873,874,875,876,877] : List (Fin 896))) :
    (result (resetState a) rf).stacks i=[] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 5
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 6
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 7
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 8
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 9
  · exact embedState_stack regMap stackMap (resetState a) _ (by decide) 11

theorem prepared_length (a : Data) (rf : Fin 8 → Bool)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670)) :
    ((result (resetState a) rf).stacks 145).length=(a.stacks 670).length := by
  rw [prepared_assignment,LeafAssignmentMergeProgram.merge_length]
  exact (Restriction.zeroMerge_spec _ _ hh).1

/-- The return-state envelope is unchanged across arbitrarily many tuple/head
visits. The larger local prefix bound is not fed back as a new input size. -/
theorem prepared_bound (a : Data) (rf : Fin 8 → Bool) (bound : ℕ)
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((result (resetState a) rf).stacks i).length≤bound := by
  intro i
  by_cases hc : i=145
  · subst i
    rw [prepared_length _ _ hh]
    exact hb 670
  · by_cases hs : i∈([872,873,874,875,876,877] : List (Fin 896))
    · rw [prepared_scratch _ _ _ hs]
      exact Nat.zero_le _
    · rw [prepared_frame _ _ i (by simpa [changed,hc] using hs)]
      exact hb i

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Actual overlay execution, including its paid reset, with the exact ambient
assignment witness retained for the source-factor interpretation. -/
theorem overlay_eval_oai {a : FactorAssignmentProgram.Data} {P n : ℕ}
    (ha : WordBound P a)
    (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hn : (a.stacks 670).length = n) :
    ∃ steps b, Eval NativeOverlay.prepare steps a b ∧ steps ≤ 70*P+70 ∧
      WordBound P b ∧ (b.stacks 145).length = n ∧
      ∀ i, i ∉ NativeOverlay.changed → b.stacks i = a.stacks i := by
  have hbits := NativeOverlay.reset_frame a 859 (by decide)
  have hmask := NativeOverlay.reset_frame a 670 (by decide)
  have hbase := NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf,hc⟩ := NativeOverlay.command_eval (NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits,hmask] using hh) (by simpa only [hmask,hbase] using hm)
  have he := (NativeOverlay.reset_eval a).seq hc
  obtain ⟨steps,rf',ht,hb,_⟩ := NativeOverlay.prepare_trace_space a P hh hm ha
  have ht' := compiled_halt_trace he 859 145
  have hsteps := StreamResources.halted_trace_steps_eq ht' ht (by rfl) (by rfl)
  refine ⟨_,_,he,by omega,NativeOverlay.prepared_bound a rf P hh ha,?_,
    NativeOverlay.prepared_frame a rf⟩
  exact (NativeOverlay.prepared_length a rf hh).trans hn

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval_oai
