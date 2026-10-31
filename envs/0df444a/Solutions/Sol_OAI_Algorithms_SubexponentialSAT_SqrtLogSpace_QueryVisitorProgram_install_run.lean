-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:32:52.10525+00:00
-- url     : https://prove2.me/submissions/bb87ed4c-ccf6-45db-882b-2f20c7283eb2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_register_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin r)
    (hi : i ∉ baseWrites c) : b.regs i = a.regs i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_register_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ baseWrites first ∧ i ∉ baseWrites second := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each register outside the static writes. -/
theorem eval_register_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin r)
    (hi : i ∉ writes c) : b.regs i = a.regs i := by
  induction ht with
  | base he => exact base_eval_register_frame he i hi
  | call p ht => exact trace_register_frame p ht i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ writes first ∧ i ∉ writes second := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Relocation changes every destination by precisely the declared register map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    registerWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (registerWrites instr).image register := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, registerWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


theorem base_code_writes {r s : ℕ} (c : StructuredProgram.Cmd r s)
    {l : ℕ} (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    registerWrites (StructuredProgram.code c embed exit q) ⊆ baseWrites c := by
  induction c generalizing l with
  | skip => exact q.elim
  | atom atom => cases atom <;> simp [StructuredProgram.code, StructuredProgram.Atom.instr,
      registerWrites, baseWrites]
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

theorem code_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    {l : ℕ} (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    registerWrites (StructuredCalls.code c embed exit q) ⊆ writes c := by
  induction c generalizing l with
  | base c => exact base_code_writes c embed exit q
  | call p =>
      simp only [StructuredCalls.code, relocate_writes, Finset.image_id, writes]
      intro i hi
      exact (mem_programWrites p i).mpr ⟨q, hi⟩
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

/-- Compiling guards, sequencing and return jumps introduces no register writes. -/
theorem compiled_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    programWrites (StructuredCalls.compiled c input output) ⊆ writes c := by
  intro i hi
  obtain ⟨label, hl⟩ := (mem_programWrites _ i).mp hi
  obtain ⟨q, rfl⟩ := (StructuredCalls.labelEquiv c).surjective label
  cases q with
  | none =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.exitAddress c)) at hl
      rw [StructuredCalls.compiled_exit] at hl
      simp [registerWrites] at hl
  | some q =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.siteAddress c q)) at hl
      rw [StructuredCalls.compiled_site] at hl
      apply code_writes c _ _ q
      exact hl

theorem not_mem_compiled {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (i : Fin r) (hi : i ∉ writes c) :
    i ∉ programWrites (StructuredCalls.compiled c input output) :=
  fun hm => hi (compiled_writes c input output hm)

/-- These primitive loops can only write their explicit value/presence registers. -/
theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
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

open CommandRegisterFrames

private theorem outside_castAdd {r k : ℕ} (i : Fin (r + k)) (hi : r ≤ i.val) :
    ¬ ∃ j : Fin r, j.castAdd k = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have := j.isLt
  simp only [Fin.val_castAdd] at hv
  omega

private theorem not_mem_union {α : Type*} [DecidableEq α] {a : α} {s t : Finset α}
    (hs : a ∉ s) (ht : a ∉ t) : a ∉ s ∪ t := by
  simpa only [Finset.mem_union, not_or] using And.intro hs ht

private theorem bank_clear_writes (tmp : Fin 896) (ports : List (Fin 896)) (i : Fin 40)
    (h0 : i ≠ 0) (h1 : i ≠ 1) :
    i ∉ writes (BankRoutines.clearCmd tmp 0 1 ports) := by
  induction ports with
  | nil => exact not_mem_clearProgram _ _ _ _ h0 h1
  | cons p ps ih =>
      exact not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1) ih

theorem overlay_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HighQueryAdapter.NativeOverlay.prepare := by
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  exact not_mem_union
    (not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1)
      (bank_clear_writes _ _ _ h0 h1))
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 8) (k := 32) i (by omega)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

theorem stagedRepresentative_words (a : Data) :
    (stagedRepresentative a).stacks 859 = a.stacks 838 ∧
    (stagedRepresentative a).stacks 670 = a.stacks 670 ∧
    (stagedRepresentative a).stacks 869 = a.stacks 869 := by
  rw [stagedRepresentative,overwriteState_stacks _ _ (by decide)]
  simp

theorem installedRepresentative_baseline (a : Data) (rf : Fin 8 → Bool) :
    (installedRepresentative a rf).stacks 869 =
      SqrtLog.LeafAssignmentMergeProgram.merge
        (SqrtLog.HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
        (a.stacks 670) (a.stacks 869) := by
  change (StackRoutines.clearStacks 859
    (overwriteState 145 869 (overlaidRepresentative a rf)).stacks) 869 = _
  simp only [StackRoutines.clearStacks,Function.update_of_ne (by decide : (869 : Fin 896) ≠ 859),
    overwriteState_stacks 145 869 (by decide),Function.update_self]
  rw [overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_assignment]
  rw [(stagedRepresentative_words a).1,(stagedRepresentative_words a).2.1,
    (stagedRepresentative_words a).2.2]

theorem installedRepresentative_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896)
    (hi : i ∉ ([145,859,869,872,873,874,875,876,877] : List (Fin 896))) :
    (installedRepresentative a rf).stacks i = a.stacks i := by
  have h859 : i ≠ 859 := by intro h; subst i; exact hi (by simp)
  have h869 : i ≠ 869 := by intro h; subst i; exact hi (by simp)
  have hover : i ∉ HighQueryAdapter.NativeOverlay.changed := by
    intro h
    simp only [HighQueryAdapter.NativeOverlay.changed,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hi (by decide)
  simp only [installedRepresentative,StackRoutines.clearStacks,Function.update_of_ne h859]
  rw [overwriteState_frame _ _ (by decide) _ _ h869,
    overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_frame _ _ _ hover,
    stagedRepresentative,overwriteState_frame _ _ (by decide) _ _ h859]

theorem installedRepresentative_bound (a : Data) (rf : Fin 8 → Bool) (B : ℕ)
    (hh : (a.stacks 838).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((installedRepresentative a rf).stacks i).length ≤ B := by
  have hs := overwriteState_bound 838 859 (by decide) a B hb
  have hsh : ((stagedRepresentative a).stacks 859).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount ((stagedRepresentative a).stacks 670) := by
    rw [(stagedRepresentative_words a).1,(stagedRepresentative_words a).2.1]
    exact hh
  have ho := HighQueryAdapter.NativeOverlay.prepared_bound (stagedRepresentative a) rf B hsh hs
  have hc := overwriteState_bound 145 869 (by decide) (overlaidRepresentative a rf) B ho
  intro i
  change (StackRoutines.clearStacks 859
    (overwriteState 145 869 (overlaidRepresentative a rf)).stacks i).length ≤ B
  by_cases hi : i = 859
  · subst i
    simp [StackRoutines.clearStacks]
  · simpa [StackRoutines.clearStacks,hi] using hc i

theorem installRepresentative_eval (a : Data) (B : ℕ)
    (htmp : a.stacks 841 = [])
    (hh : (a.stacks 838).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
      steps ≤ 90 * B + 89 := by
  have hcopy := overwrite_eval 838 859 (by decide) (by decide) (by decide) a htmp
  have hstage := stagedRepresentative_words a
  have hs := overwriteState_bound 838 859 (by decide) a B hb
  have hsh : ((stagedRepresentative a).stacks 859).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount ((stagedRepresentative a).stacks 670) := by
    rw [hstage.1,hstage.2.1]
    exact hh
  obtain ⟨nt,rf,htr,hcost,_⟩ := HighQueryAdapter.NativeOverlay.prepare_trace_space
    (stagedRepresentative a) B hsh (by simpa only [hstage.2.1,hstage.2.2] using hm) hs
  have he : Eval (.call HighQueryAdapter.NativeOverlay.prepareProgram) nt
      (stagedRepresentative a) (overlaidRepresentative a rf) := Eval.call _ htr
  have h841 : (overlaidRepresentative a rf).stacks 841 = [] := by
    rw [overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_frame _ _ _ (by decide),
      stagedRepresentative,overwriteState_frame _ _ (by decide) _ _ (by decide)]
    exact htmp
  have hsave := overwrite_eval 145 869 (by decide) (by decide) (by decide)
    (overlaidRepresentative a rf) h841
  have hclear := clear_eval 859 (overwriteState 145 869 (overlaidRepresentative a rf))
  have hout := hcopy.seq (he.seq (hsave.seq hclear))
  refine ⟨_,rf,hout,?_⟩
  have hbo := HighQueryAdapter.NativeOverlay.prepared_bound (stagedRepresentative a) rf B hsh hs
  have hbc := overwriteState_bound 145 869 (by decide) (overlaidRepresentative a rf) B hbo
  have h859 := hb 859
  have h838 := hb 838
  have h869 := hbo 869
  have h145 := hbo 145
  have hlast := hbc 859
  change ((overlaidRepresentative a rf).stacks 869).length ≤ B at h869
  change ((overlaidRepresentative a rf).stacks 145).length ≤ B at h145
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end DenseWord

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Static register frames for the concrete tuple visitor. The frame follows
from the actual instructions and embeddings, including the ambient overlay.
The retained tuple-controller flags require no save stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

open OAI BitProgram StructuredCalls
open CommandRegisterFrames QueryTupleVisitor

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val)
    (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro h
  subst i
  omega

private theorem copy_not_mem_writes (src dst tmp : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (SignatureTupleProgram.copyWord src dst tmp) :=
  not_mem_copyProgram src dst tmp 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

theorem overwrite_not_mem_writes (src dst : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes (overwrite src dst) :=
  not_mem_union_iff.mpr ⟨not_mem_clearProgram dst 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)),
    copy_not_mem_writes src dst 841 i hi⟩

theorem install_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes installRepresentative :=
  not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 838 859 i hi,
    not_mem_union_iff.mpr ⟨not_mem_compiled _ _ _ i
      (HeadSumAssembly.overlay_not_mem_writes i hi),
      not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 145 869 i hi,
        not_mem_clearProgram 859 0 1 i
          (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))⟩⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

theorem installed_masterFrame (a : Data) (rf : Fin 8 → Bool) :
    QueryMasterFrame a (installedRepresentative a rf) := by
  constructor
  intro i hi
  have hs : i∉([145,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact installedRepresentative_frame a rf i hs

/-- The first-pass native overlay updates only the ambient representative
baseline. All ring inputs, the tuple product and the pair accumulator retain
their actual words and denotations. -/
theorem install_run_oai {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (htmp : a.stacks 841=[])
    (hh : (a.stacks 838).length=HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hmask : (a.stacks 670).length=(a.stacks 869).length) :
    ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
      QueryReady q node H high E U P (installedRepresentative a rf) ∧
      PairAccumulatorMeaning q pairValue (installedRepresentative a rf) ∧
      DenseWord q 852 tupleValue (installedRepresentative a rf) ∧
      QueryMasterFrame a (installedRepresentative a rf) ∧
      WordBound B (installedRepresentative a rf) ∧
      (installedRepresentative a rf).stacks 869=
        LeafAssignmentMergeProgram.merge
          (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
          (a.stacks 670) (a.stacks 869) ∧
      (∀ i : Fin 40,16 ≤ i.val → (installedRepresentative a rf).regs i=a.regs i) ∧
      steps≤90*B+89 ∧
      QueryExecution.PrefixBound installRepresentative steps a (986*B+89) := by
  obtain ⟨steps,rf,he,ht⟩ := installRepresentative_eval a B htmp hh hmask ha
  have hf:=installed_masterFrame a rf
  refine ⟨steps,rf,he,hr.frame hf,
    hm.frame (installedRepresentative_frame a rf 851 (by decide)),
    hv.frame (installedRepresentative_frame a rf 852 (by decide)),hf,
    installedRepresentative_bound a rf B hh ha,installedRepresentative_baseline a rf,?_,ht,?_⟩
  · intro i hi
    exact CommandRegisterFrames.eval_register_frame he i
      (QueryVisitorFrames.install_not_mem_writes i hi)
  · exact (QueryExecution.prefix_local installRepresentative steps B a ha).mono (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run_oai
