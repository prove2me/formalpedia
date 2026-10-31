-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:36:15.40198+00:00
-- url     : https://prove2.me/submissions/e473b02e-5896-49d2-b99f-06c845e68b08

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighBranchSpace_prepare_high_space

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

theorem encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id words).length =
      2 * words.flatten.length + 2 * words.length + 1 := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    rw [Encoding.length_encodeList_cons]
    simp only [id_eq, List.flatten_cons, List.length_append, List.length_cons]
    omega

end SubexponentialSAT.ExecCNFTupleOdometer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual overflow-controlled enumeration of framed binary tuples

The callback is fixed executable code. Every iteration invokes it and then
invokes the concrete framed odometer, including the final overflow increment.
The number and widths of records are never part of finite control.
-/

namespace SubexponentialSAT.ExecCNFTupleEnumeration

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open ExecCNFTupleOdometer

variable {R S : ℕ}

theorem tuple_eq_of_shape_flatten {a b : List (List Bool)}
    (hshape : a.map List.length = b.map List.length) (hflat : a.flatten = b.flatten) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp at hshape
  | cons x xs ih =>
    cases b with
    | nil => simp at hshape
    | cons y ys =>
      change x.length :: xs.map List.length = y.length :: ys.map List.length at hshape
      obtain ⟨hl, hrest⟩ := List.cons.inj hshape
      change x ++ xs.flatten = y ++ ys.flatten at hflat
      have hx : x = y := List.append_inj_left hflat hl
      have ht : xs.flatten = ys.flatten := List.append_inj_right hflat hl
      exact congrArg₂ List.cons hx (ih hrest ht)

/-- Fixed component widths and payload rank uniquely identify the tuple. -/
theorem tuple_eq_of_shape_value {a b : List (List Bool)}
    (hshape : a.map List.length = b.map List.length)
    (hv : CounterPrograms.value a.flatten = CounterPrograms.value b.flatten) : a = b := by
  have hl : a.flatten.length = b.flatten.length := by
    simpa only [List.length_flatten] using congrArg List.sum hshape
  exact tuple_eq_of_shape_flatten hshape (word_eq_of_length_value hl hv)

end SubexponentialSAT.ExecCNFTupleEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

theorem assignment_value (h : ℕ) (r : Fin (2 ^ h)) :
    CounterPrograms.value (List.ofFn (assignment h r)) = r.val := by
  exact congrArg Fin.val ((rankEquiv h).apply_symm_apply r)

theorem tuple_of_rank {h : ℕ} (words : List (List Bool))
    (hshape : words.map List.length = List.replicate h 1)
    (r : Fin (2 ^ h)) (hr : CounterPrograms.value words.flatten = r.val) :
    words = (List.ofFn (assignment h r)).map (fun b => [b]) := by
  apply ExecCNFTupleEnumeration.tuple_eq_of_shape_value
  · simpa [List.map_map, Function.comp_def] using hshape
  · have hflat : ((List.ofFn (assignment h r)).map (fun b => [b])).flatten =
          List.ofFn (assignment h r) := by
        generalize List.ofFn (assignment h r) = xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [ih]
    rw [hflat]
    exact hr.trans (assignment_value h r).symm

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

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

theorem highOrder_val {n : ℕ} (H : Finset (Fin n)) (i : Fin H.card) :
    (highOrder H i).val = (highCoordinates H).get
      ⟨i.val, by simp⟩ := by
  rfl

theorem highOrder_stream {n : ℕ} (H : Finset (Fin n)) (x : Fin n → Bool) :
    List.ofFn (fun i : Fin H.card => x (highOrder H i)) = (highCoordinates H).map x := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [ highOrder_val, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramShiftSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-variable meaning of the physical high-value vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem zeroMerge_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    zeroMerge (xs.map p) ((xs.filter p).map x) =
      xs.map (fun v => if p v then x v else false) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [zeroMerge, merge, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem runsIn (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
    (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ rf, RunsIn program (cost words mask+1)
      ((state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] []).withPC
        (some program.entry))
      ((state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
        (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] []).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval regs words mask hh
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 3⟩


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

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

theorem highResult_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 896) (hi : i ∉ highChanged) :
    (highResult a regs high).stacks i = a.stacks i := by
  by_cases hx : ∃ j, highStacks j = i
  · obtain ⟨j,rfl⟩ := hx
    rw [show (highResult a regs high).stacks (highStacks j) =
      (LeafHighContextProgram.Local.state regs (a.stacks 330) (a.stacks 338)
        (a.stacks 338).reverse (Restriction.zeroMerge (a.stacks 338) high).reverse
        [] [] [] [] [] []).stacks j from
      embedState_stack highRegs highStacks a _ (by decide) j]
    fin_cases j <;> simp_all [highStacks,highChanged,LeafHighContextProgram.Local.state,
      LeafHighContextProgram.Local.tapes]
  · exact embedState_stack_frame highRegs highStacks a _ i hx

/-- The high vector is extracted from the actual encoded current tuple. Its
master counter and mask remain available for later odometer iterations. -/
theorem high_eval (a : Data) (words : List (List Bool)) (h : ℕ)
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (he : ∀ i ∈ highChanged, a.stacks i = [])
    (hshape : words.map List.length = List.replicate h 1)
    (hh : h = Restriction.highCount (a.stacks 338)) :
    ∃ steps regs, steps ≤ 22 * (a.stacks 338).length + 43 * h + 37 ∧
      Eval highCommand steps a (highResult a regs words.flatten) := by
  have hw : words.length = h := by
    have ht := congrArg List.length hshape
    simpa only [List.length_map,List.length_replicate] using ht
  have hf : words.flatten.length = h := by
    rw [List.length_flatten,hshape]
    simp
  have henc : (ProgramEncoding.encodeRecords words).length = 4*h+1 := by
    rw [show ProgramEncoding.encodeRecords words = Encoding.encodeList id words from rfl,
      ExecCNFTupleOdometer.encoded_length,hf,hw]
    omega
  obtain ⟨rf,⟨steps,hn,ht⟩⟩ := LeafHighContextProgram.Local.runsIn
    (a.regs ∘ highRegs) words (a.stacks 338) (hf.trans hh)
  have hp : projectState highRegs highStacks a =
      LeafHighContextProgram.Local.state (a.regs ∘ highRegs)
        (ProgramEncoding.encodeRecords words) (a.stacks 338) [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [highStacks,
        LeafHighContextProgram.Local.tapes,hc,
        he 702 (by simp [highChanged]),he 703 (by simp [highChanged]),
        he 680 (by simp [highChanged]),he 681 (by simp [highChanged]),
        he 682 (by simp [highChanged]),he 683 (by simp [highChanged]),
        he 684 (by simp [highChanged]),he 685 (by simp [highChanged])]
  rw [← hp] at ht
  have hex := eval_call_from_state LeafHighContextProgram.Local.program highRegs highStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  refine ⟨steps,rf,?_,?_⟩
  · unfold LeafHighContextProgram.Local.cost at hn
    rw [henc,hf,hw] at hn
    omega
  · simpa only [highCommand,highResult,hc] using hex

/-- The produced fixed-high values have their original ambient IDs. -/
theorem high_vector_semantics {n : ℕ} (H : Finset (Fin n)) (high : H → Bool) :
    (Restriction.zeroMerge (SqrtLogSpace.HighIncidenceProgram.descendingHighMask H)
      (List.ofFn (fun i => high (Order.highOrder H i)))).reverse =
      List.ofFn (HighIncidence.glue H high (fun _ => false)) := by
  let x := HighIncidence.glue H high (fun _ => false)
  have hhigh : List.ofFn (fun i => high (Order.highOrder H i)) =
      (Order.highCoordinates H).map x := by
    rw [← Order.highOrder_stream]
    congr 1
    funext i
    simp [x,HighIncidence.glue,(Order.highOrder H i).property]
  rw [hhigh]
  unfold SqrtLogSpace.HighIncidenceProgram.descendingHighMask Order.highCoordinates
  rw [Restriction.zeroMerge_map]
  have hx : (fun v => if decide (v ∈ H) then x v else false) = x := by
    funext v
    by_cases hv : v ∈ H <;> simp [hv,x,HighIncidence.glue]
  rw [hx,Order.coordinates_stream,List.reverse_reverse]

theorem resetHigh_eval (a : Data) : Eval resetHigh (resetHighCost a) a (resetHighState a) := by
  have h1 := BankRoutines.clear_call_eval (702 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (702 : Fin 896) (0 : Fin 40) 1 highChanged (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 702 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks highChanged (StackRoutines.clearStacks 702 a.stacks) =
      BankRoutines.clearBankStacks highChanged a.stacks := by
    funext i
    by_cases hi : i ∈ highChanged
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 702 := by intro h; subst i; exact hi (by simp [highChanged])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [resetHigh,resetHighCost,resetHighState,show highChanged.length=8 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem resetHigh_frame (a : Data) (i : Fin 896) (hi : i ∉ highChanged) :
    (resetHighState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i highChanged a.stacks hi

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual high-condition staging uses a fixed local ten-stack footprint.
The independent physical cap is never identified with a sum of caller words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The actual one-bit tuple odometer is decoded in the descending physical
high-coordinate order, then returned to ascending ambient coordinates. -/
theorem rank_high_vector_semantics {n : ℕ} (H : Finset (Fin n))
    (words : List (List Bool)) (hshape : words.map List.length=List.replicate H.card 1)
    (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val) :
    (Restriction.zeroMerge (SqrtLogSpace.HighIncidenceProgram.descendingHighMask H)
      words.flatten).reverse =
      List.ofFn (HighIncidence.glue H (Rank.highEquiv (Order.highOrder H) rank)
        (fun _ => false)) := by
  have ht := Rank.tuple_of_rank words hshape rank hrank
  have hflat : words.flatten=List.ofFn (Rank.assignment H.card rank) := by
    rw [ht]
    generalize List.ofFn (Rank.assignment H.card rank)=xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have horder : List.ofFn (fun i =>
      Rank.highEquiv (Order.highOrder H) rank (Order.highOrder H i)) =
      List.ofFn (Rank.assignment H.card rank) := by
    congr 1
    funext i
    simp [Rank.highEquiv,Rank.reindex,Rank.assignment]
  rw [hflat,←horder]
  exact high_vector_semantics H (Rank.highEquiv (Order.highOrder H) rank)

private theorem high_scratch (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 896) (hi : i∈([680,681,682,683,684,685] : List (Fin 896))) :
    (highResult a regs high).stacks i=[] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact embedState_stack highRegs highStacks a _ (by decide) 4
  · exact embedState_stack highRegs highStacks a _ (by decide) 5
  · exact embedState_stack highRegs highStacks a _ (by decide) 6
  · exact embedState_stack highRegs highStacks a _ (by decide) 7
  · exact embedState_stack highRegs highStacks a _ (by decide) 8
  · exact embedState_stack highRegs highStacks a _ (by decide) 9

/-- Exact outputs are ambient-length words; all consumed parser buffers are
empty. This is the repeated boundary invariant, independently of transient cost. -/
theorem result_bound (a : Data) (regs : Fin 4 → Bool) (high : List Bool) (bound : ℕ)
    (hh : high.length=Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((highResult a regs high).stacks i).length≤bound := by
  intro i
  by_cases hm : i=702
  · subst i; rw [highResult_mask,List.length_reverse]; exact hb 338
  · by_cases hh' : i=703
    · subst i
      rw [highResult_bits,List.length_reverse,(Restriction.zeroMerge_spec _ _ hh).1]
      exact hb 338
    · by_cases hs : i∈([680,681,682,683,684,685] : List (Fin 896))
      · rw [high_scratch a regs high i hs]; exact Nat.zero_le _
      · rw [highResult_frame a regs high i (by simpa [highChanged,hm,hh'] using hs)]
        exact hb i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem descendingMask_eq (H : Finset (Fin n)) :
    descendingMask H=(List.ofFn (fun v : Fin n=>decide (v∈H))).reverse :=
  Order.coordinates_stream n _

theorem descendingMask_count (H : Finset (Fin n)) :
    Branches.trueCount (descendingMask H)=H.card := by
  have he : ((descendingMask H).filter id).length=(Order.highCoordinates H).length := by
    unfold descendingMask Order.highCoordinates
    rw [List.filter_map]
    simp
  exact he.trans (Order.highCoordinates_length H)

theorem flattened_length (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) : words.flatten.length=H.card := by
  rw [List.length_flatten,hshape]
  simp

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual current-high decoder, kept independent of the complete query
and high-loop composition so the fixed stream can consume its proved run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount
open HashGreedyProgram.NativeRound

/-- Actual entry of the fixed conditioned stream. Cleanup is charged only
on its eight touched words, and decoding uses the physical current counter
and current descending mask. The output restores the original compact cap. -/
theorem prepare_high_resources_oai {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1)
    (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val)
    (a : Data) (P B : ℕ)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hcounter : (a.stacks 330).length≤P) (hmask : (a.stacks 338).length≤P)
    (hchanged : ∀ i∈highChanged,(a.stacks i).length≤P)
    (hB : ∀ i,(a.stacks i).length≤B) :
    ∃ steps rf, let b := highResult (resetHighState a) rf words.flatten
      Eval prepareHigh steps a b ∧ steps≤18*P+65*n+67 ∧
      b.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H)) ∧
      b.stacks 703=List.ofFn (HighIncidence.glue H
        (SqrtLog.HighIncidenceProgram.Rank.highEquiv
          (SqrtLog.HighIncidenceProgram.Order.highOrder H) rank) (fun _ => false)) ∧
      (∀ i,i∉highChanged → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤B) ∧
      StageSpace prepareHigh (steps+1) a (max (67*P+37) B) := by
  have hmaskLength : (a.stacks 338).length=n := by
    rw [hm]
    simp [HighIncidenceProgram.descendingHighMask,SqrtLog.HighIncidenceProgram.Order.coordinates]
  have hcount : H.card=SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 338) := by
    rw [hm]
    exact (PreparedBranchCount.descendingMask_count H).symm
  have hmr := resetHigh_frame a 338 (by decide)
  have hcr := resetHigh_frame a 330 (by decide)
  have hresetBound : ∀ i,((resetHighState a).stacks i).length≤B := by
    intro i
    by_cases hi : i∈highChanged
    · simp [resetHighState,BankRoutines.clearBankStacks,hi]
    · rw [resetHigh_frame a i hi]
      exact hB i
  obtain ⟨localSteps,rf,ht,he⟩ := high_eval (resetHighState a) words H.card
    (hcr.trans hc) (fun i hi => BankRoutines.clearBankStacks_mem i highChanged a.stacks hi)
    hshape (by rw [hmr]; exact hcount)
  have hsum : (highChanged.map
      (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)).sum≤8*P := by
    have hb : ∀ i∈highChanged,((StackRoutines.clearStacks 702 a.stacks) i).length≤P := by
      intro i hi
      by_cases hz : i=702
      · subst i
        simp [StackRoutines.clearStacks]
      · simpa only [StackRoutines.clearStacks,Function.update_of_ne hz] using hchanged i hi
    have hh := List.sum_le_card_nsmul
      (highChanged.map (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)) P
      (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hb i hi)
    simpa only [List.length_map,show highChanged.length=8 from rfl,smul_eq_mul] using hh
  have hresetTime : resetHighCost a≤18*P+30 := by
    have ht := hchanged 702 (by decide)
    unfold resetHighCost
    omega
  have hdim : H.card≤n := by simpa using Finset.card_le_univ H
  have htime : resetHighCost a+localSteps≤18*P+65*n+67 := by
    rw [hmr,hmaskLength] at ht
    omega
  have whole := (resetHigh_eval a).seq he
  obtain ⟨prefixSteps,otherRegs,htrace,_,hprefix⟩ := HighBranchSpace.prepare_high_space
    a words H.card P (max (67*P+37) B) 778 777 hc hshape hcount hcounter hmask
    (Nat.le_max_left _ _)
    (fun i => (hB i).trans (Nat.le_max_right _ _))
  have hsame : prefixSteps=resetHighCost a+localSteps+1 :=
    StreamResources.halted_trace_steps_eq htrace (compiled_halt_trace whole 778 777) rfl rfl
  refine ⟨_,rf,whole,htime,?_,?_,?_,?_,?_⟩
  · rw [highResult_mask,hmr,hm]
    change (PreparedBranchCount.descendingMask H).reverse=_
    rw [PreparedBranchCount.descendingMask_eq,List.reverse_reverse]
  · rw [highResult_bits,hmr,hm]
    exact HighBranchSpace.rank_high_vector_semantics H words hshape rank hrank
  · intro i hi
    exact (highResult_frame _ rf words.flatten i hi).trans (resetHigh_frame a i hi)
  · apply HighBranchSpace.result_bound _ rf words.flatten B _ hresetBound
    rw [PreparedBranchCount.flattened_length H words hshape,hmr]
    exact hcount
  · constructor
    simpa only [hsame] using hprefix

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources_oai
