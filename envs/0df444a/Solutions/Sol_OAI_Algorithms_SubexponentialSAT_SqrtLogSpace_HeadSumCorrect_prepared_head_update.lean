-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:26:57.640508+00:00
-- url     : https://prove2.me/submissions/980262a9-8636-4ae8-b58c-491b8a68bad8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryAdapter_NativeOverlay_command_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem selected_true_length (mask xs : List Bool) (hlen : mask.length = xs.length) :
    (selected true mask xs).length = Subexp.PaddedCompletion.trueCount mask := by
  induction mask generalizing xs with
  | nil => simp [selected, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have ht : mask.length = xs.length := by simpa using hlen
          cases b <;> simp [selected, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful] at * <;> exact ih xs ht

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical scan merges a current-head assignment with the bucket
representative, keeping the original ambient coordinate order. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem merge_ofFn {n : ℕ} (a h b : Fin n → Bool) :
    merge (List.ofFn a) (List.ofFn h) (List.ofFn b) =
      List.ofFn (fun i => if h i then a i else b i) := by
  induction n with
  | zero => simp [merge]
  | succ n ih => simp [List.ofFn_succ,merge,ih]

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadRepresentativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

/-- Updating the owned head in the reconstructed representative preserves
all foreign-head bits, including fixed-high coordinates. -/
theorem merge_candidate_ofFn {n : ℕ} {G : Type*} [DecidableEq G]
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → G)
    (reps : ∀ g,Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (g : G) (candidate : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (current : Fin n → Bool)
    (hcurrent : ∀ v (hv : v∉H) (hg : head v=g),current v=candidate ⟨⟨v,hv⟩,hg⟩) :
    merge (List.ofFn current) (List.ofFn (fun v => decide (v∉H ∧ head v=g)))
      (List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val)
          (Function.update reps g candidate))) := by
  rw [merge_ofFn]
  apply congrArg List.ofFn
  funext v
  by_cases hv : v∈H
  · simp [hv,HighIncidence.glue]
  · by_cases hg : head v=g
    · subst g
      simp [hv,HighIncidence.glue,Moments.assemble,hcurrent v hv rfl]
    · simp [hv,hg,HighIncidence.glue,Moments.assemble]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HeadIdentifierProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The actual chosen-ID word fixes the ascending selection order. -/
theorem headOrder_stream (p : ℕ → Bool) (n : ℕ) :
    (List.finRange n).filter (fun v => p v.val)=List.ofFn (headOrder p n) := by
  apply (List.map_injective_iff.mpr (Fin.val_injective : Function.Injective (Fin.val (n:=n))))
  rw [List.map_ofFn]
  change _=HeadScatterProgram.headIds (headOrder p n)
  rw [headOrder_ids]
  simpa only [List.map_coe_finRange,chosenIds,Function.comp_def] using
    (List.filter_map (f:=(Fin.val : Fin n → ℕ)) (p:=p) (l:=List.finRange n)).symm

/-- The native selected-bit scan emits exactly the current head's ambient
coordinates in the already emitted headOrder, including the empty head. -/
theorem selected_headOrder (p : ℕ → Bool) (n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn x) =
      List.ofFn (fun i => x (headOrder p n i)) := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,Order.selected_map,headOrder_stream,List.map_ofFn]
  rfl

/-- The physical selected-mask population is the actual emitted head width. -/
theorem headOrder_highCount (p : ℕ → Bool) (n : ℕ) :
    Restriction.highCount (List.ofFn (fun v : Fin n => p v.val))=count p n := by
  have hh := Restriction.selected_true_length (List.ofFn (fun v : Fin n => p v.val))
    (List.ofFn (fun _ : Fin n => true)) (by simp)
  rw [selected_headOrder,List.length_ofFn] at hh
  exact hh.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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



@[simp] theorem prepared_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result (resetState a) rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) := by
  rw [result_assignment,reset_frame a 670 (by decide),reset_frame a 859 (by decide),
    reset_frame a 869 (by decide)]

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

/-- The actual zero-filled ambient word contains the current raw candidate
at exactly the ascending head coordinates used by the matrix columns. -/
theorem zeroMerge_headOrder (p : ℕ → Bool) (n : ℕ)
    (bits : Fin (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count p n) → Bool) :
    ∃ current : Fin n → Bool,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge
        (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn bits) = List.ofFn current ∧
      ∀ i, current (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.headOrder p n i) = bits i := by
  let mask := List.ofFn (fun v : Fin n => p v.val)
  let xs := OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge mask (List.ofFn bits)
  have hs := OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge_spec mask (List.ofFn bits)
    (by simp [mask, HeadRepresentativeSemantics.headOrder_highCount])
  have hlen : xs.length = n := by simpa [xs, mask] using hs.1
  have hex : ∃ current : Fin xs.length → Bool, xs = List.ofFn current :=
    ⟨fun i => xs[i.val], (List.ofFn_getElem (xs := xs)).symm⟩
  rw [hlen] at hex
  obtain ⟨current, hcurrent⟩ := hex
  refine ⟨current, hcurrent, ?_⟩
  have hselect := hs.2.1
  change OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true mask xs = _ at hselect
  rw [hcurrent, HeadRepresentativeSemantics.selected_headOrder] at hselect
  exact congrFun (List.ofFn_injective hselect)

/-- The concrete overlay preserves the ambient coordinate count and changes
only the current head, using the existing representative/high baseline. -/
theorem prepared_head_assignment (a : Data) (rf : Fin 8 → Bool)
    (p : ℕ → Bool) (n : ℕ)
    (bits : Fin (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count p n) → Bool)
    (baseline : Fin n → Bool)
    (hbits : a.stacks 859 = List.ofFn bits)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
    (hbase : a.stacks 869 = List.ofFn baseline) :
    ∃ current : Fin n → Bool,
      (∀ i, current (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.headOrder p n i) = bits i) ∧
      (HighQueryAdapter.NativeOverlay.result
        (HighQueryAdapter.NativeOverlay.resetState a) rf).stacks 145 =
        List.ofFn (fun v => if p v.val then current v else baseline v) := by
  obtain ⟨current, hcurrent, hhead⟩ := zeroMerge_headOrder p n bits
  refine ⟨current, hhead, ?_⟩
  rw [HighQueryAdapter.NativeOverlay.prepared_assignment, hbits, hmask, hbase,
    hcurrent, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.merge_ofFn]

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Semantic correctness of the concrete head accumulator. Native dictionary
witnesses are retained only for the current partial sum, and their meaning is
proved using the actual finite-ring normalization program. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators


open HeadIdentifierProgram

/-- The reviewed source order equivalence names the same positions as the
actual head-size word and ID stream; it introduces no executable reindexing. -/
theorem freeOrder_eq_headOrder {n r : ℕ} (H : Finset (Fin n))
    (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (i : Fin (count p n)) :
    (BucketTupleProgram.Concrete.freeOrder H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs i).val.val = headOrder p n i := rfl

/-- The paid ambient overlay realizes exactly the candidate substitution used
by restricted grouping, while retaining the fixed-high assignment. -/
theorem prepared_head_update_oai {n r : ℕ} (H : Finset (Fin n))
    (high : H → Bool) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ _ : v ∉ H, head v = g)
    (reps : ∀ k, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) k → Bool)
    (candidate : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
    {steps : ℕ} (a b : HeadSumProgram.Data)
    (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
    (hbits : a.stacks 859 = List.ofFn
      (BucketTupleProgram.Concrete.freeAssignmentEquiv H
        (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps))) :
    b.stacks 145 =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val)
          (Function.update reps g candidate))) := by
  have hh : (a.stacks 859).length =
      HighIncidenceProgram.Restriction.highCount (a.stacks 670) := by
    simp [hbits, hmask, HeadRepresentativeSemantics.headOrder_highCount, count]
  have hm : (a.stacks 670).length = (a.stacks 869).length := by
    simp [hmask, hbase]
  have hbits' := HighQueryAdapter.NativeOverlay.reset_frame a 859 (by decide)
  have hmask' := HighQueryAdapter.NativeOverlay.reset_frame a 670 (by decide)
  have hbase' := HighQueryAdapter.NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf, hc⟩ := HighQueryAdapter.NativeOverlay.command_eval
    (HighQueryAdapter.NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i
      HighQueryAdapter.NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits', hmask'] using hh)
    (by simpa only [hmask', hbase'] using hm)
  have heq := Eval.final_unique (859 : Fin 896) he
    ((HighQueryAdapter.NativeOverlay.reset_eval a).seq hc)
  rw [heq]
  let order := BucketTupleProgram.Concrete.freeOrder H
    (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs
  obtain ⟨current, hcurrent, hout⟩ := HeadSumAssembly.prepared_head_assignment a rf p n
    _ _ hbits hmask hbase
  have hm : (fun v : Fin n => p v.val) = (fun v => decide (v ∉ H ∧ head v = g)) := by
    funext v
    have hv := hs v
    simp only [chosenIds, List.mem_filter, List.mem_range, v.isLt, true_and,
      exists_prop] at hv
    exact Bool.eq_iff_iff.mpr (by simpa using hv)
  have hc : ∀ v (hv : v ∉ H) (hg : head v = g), current v = candidate ⟨⟨v, hv⟩, hg⟩ := by
    intro v hv hg
    let w : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g := ⟨⟨v, hv⟩, hg⟩
    have ho := order.apply_symm_apply w
    have hval : headOrder p n (order.symm w) = v := by
      have horder := freeOrder_eq_headOrder H
        (fun v : {v : Fin n // v ∉ H} => head v.val) g p hs (order.symm w)
      exact horder.symm.trans ((congrArg
        (fun x : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g =>
          x.val.val) ho).trans rfl)
    have hx := hcurrent (order.symm w)
    change current (headOrder p n (order.symm w)) = candidate (order (order.symm w)) at hx
    simpa only [hval, ho] using hx
  simp_rw [congrFun hm] at hout
  rw [← LeafAssignmentMergeProgram.merge_ofFn] at hout
  exact hout.trans (HeadRepresentativeSemantics.merge_candidate_ofFn H high head reps g
    candidate current hc)

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update_oai
