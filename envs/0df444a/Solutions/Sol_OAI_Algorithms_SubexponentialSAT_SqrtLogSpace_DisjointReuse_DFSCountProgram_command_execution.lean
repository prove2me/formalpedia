-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:16.510113+00:00
-- url     : https://prove2.me/submissions/86b402b9-70e8-43f7-9886-7c38235f8e9e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSNative_normalized_loop
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

section Decidable

section Finite

variable [Fintype V]

theorem count_le (F : CNF V) : count F ≤ 2 ^ Fintype.card V := by
  calc
    count F ≤ (Finset.univ : Finset (Assignment V)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card V := by simp [Assignment ]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse


theorem rawCount_le {n : ℕ} (F : RawCNF n) : rawCount F ≤ 2 ^ n := by
  simpa [rawCount] using SAT.count_le (ExecCNF.formulaSet F)

theorem binaryNat_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (binaryNat a).length ≤ n + 1 := by
  by_cases hzero : a = 0
  · simp [binaryNat, hzero]
  · simpa only [binaryNat, ite_eq_right hzero, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- Sequential command blocks share one uniform space bound. -/
theorem sequence_stack_bound {r s L : ℕ} {first second : StructuredCalls.Cmd r s}
    {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (hf : StructuredCalls.Eval first n a b) (hs : StructuredCalls.Eval second m b c)
    (inputStack outputStack : Fin s)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled first inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled first inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled second inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled second inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.seq first second) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.seq first second) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.seq first second) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  exact trace_prefix_bound_trans
    (StructuredCalls.eval_trace hf caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hf inputStack outputStack hfirst caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hs inputStack outputStack hsecond caller (embed ∘ Sum.inr)
      exit (fun q => hcode (.inr q)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem transfer_eval (src dst : Fin 4) (hsd : src ≠ dst) (d : State 3 4) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩ := by
  exact Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide)
    d.regs d.stacks)

theorem push_eval (body saved pending : List Bool) (v p flag : Bool) :
    Eval push (8 * body.length + 10)
      (state v p flag body saved pending [])
      (state true false flag [] saved (true :: (Encoding.frame body ++ pending)) []) := by
  have ht : Eval (transfer 0 3) (3 * body.length + 3)
      (state v p flag body saved pending [])
      (state false false flag [] saved pending body.reverse) := by
    simpa [state, SubexpNormalizeProgram.filterState, StackRoutines.transferStacks,
      readRegs] using transfer_eval 0 3 (by decide)
        (state v p flag body saved pending [])
  have he := Eval.call _
    (SubexpNormalizeProgram.emitRecord_trace body [] saved pending false false flag)
  convert ht.seq he using 1 <;> first | rfl | omega

theorem initFrontier_eval (body saved : List Bool) (v p flag : Bool) :
    Eval initFrontier (8 * body.length + 12)
      (state v p flag body saved [] [])
      (state true false flag [] saved (Encoding.encodeList id [body]) []) := by
  have hs : Eval (.base (.seq (.atom (.set (0 : Fin 3) false))
      (.atom (.push (2 : Fin 4) 0)))) 2
      (state v p flag body saved [] []) (state false p flag body saved [false] []) := by
    have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false)
      (state v p flag body saved [] [])).seq
        (StructuredProgram.Eval.atom (.push (2 : Fin 4) (0 : Fin 3)) _)
    simpa [state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
      StructuredProgram.State.ofCfg, execInstr] using Eval.base h
  have hp := push_eval body saved [false] false p flag
  have h := hs.seq hp
  change Eval initFrontier (2 + (8 * body.length + 10)) _ _ at h
  convert h using 1
  · ring
  · simp [Encoding.encodeList]

theorem initFrontier_trace (body saved : List Bool) (v p flag : Bool) :
    Trace initFrontierProgram (8 * body.length + 13)
      ((state v p flag body saved [] []).withPC (some initFrontierProgram.entry))
      ((state true false flag [] saved (Encoding.encodeList id [body]) []).withPC none) := by
  simpa only [initFrontierProgram, Nat.add_assoc] using compiled_halt_trace
    (initFrontier_eval body saved v p flag) 0 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem testPending_eval (d : Data) :
    Eval testPending 1 d
      ⟨readRegs d.regs 2 1 (d.stacks 257).head?, d.stacks⟩ := by
  simpa [testPending, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr]
    using Eval.base (StructuredProgram.Eval.atom (.peek (257 : Fin 1220) (2 : Fin 80) 1) d)

theorem startTotal_eval (d : Data) (htotal : d.stacks 260 = []) :
    Eval startTotal 2 d
      ⟨Function.update d.regs 0 false, Function.update d.stacks 260 [false]⟩ := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 80) false) d).seq
    (StructuredProgram.Eval.atom (.push (260 : Fin 1220) (0 : Fin 80)) _)
  simpa [startTotal, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, htotal]
    using Eval.base h

theorem clearPort_eval (port : Fin 1220) (d : Data) :
    Eval (clearPort port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

theorem exportCount_eval (d : Data) :
    ∃ e, Eval exportCount
      (2 * (d.stacks 0).length + 2 * (d.stacks 256).length +
        7 * (d.stacks 260).length + 11) d e ∧
      e.stacks 256 = d.stacks 260 ∧ e.stacks 0 = [] ∧
      ∀ i, i ≠ 0 → i ≠ 256 → e.stacks i = d.stacks i := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 0 d.stacks⟩
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 256 a.stacks⟩
  have h0 : b.stacks 0 = [] := by simp [b, a, StackRoutines.clearStacks]
  have hout : b.stacks 256 = [] := by simp [b, StackRoutines.clearStacks]
  have htotal : b.stacks 260 = d.stacks 260 := by
    simp [b, a, StackRoutines.clearStacks]
  have h256 : a.stacks 256 = d.stacks 256 := by simp [a, StackRoutines.clearStacks]
  have hcopy : Eval (.call (StackRoutines.copyProgram 260 256 0 0 1))
      (7 * (b.stacks 260).length + 5) b
      ⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 260 256 b.stacks⟩ :=
    Eval.call _ (ListRegisterProgram.copy_run (r := 80) (s := 1220)
      260 256 0 0 1 (by decide) (by decide) (by decide) (by decide) b.regs b.stacks h0)
  have hrun := (clearPort_eval 0 d).seq ((clearPort_eval 256 a).seq hcopy)
  refine ⟨⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 260 256 b.stacks⟩,
    ?_, ?_, ?_, ?_⟩
  · convert hrun using 1
    · rfl
    · simp [htotal, h256]
      omega
  · simp [StackRoutines.copyStacks, hout, htotal]
  · simp [StackRoutines.copyStacks, h0]
  · intro i hi0 hi256
    simp [StackRoutines.copyStacks, b, a, StackRoutines.clearStacks, hi0, hi256]

/-- Output cleanup and copying use only their own linear work, never the
exponentially long traversal time; every one of the 1220 stacks is counted. -/
theorem exportCount_prefix_space (d : Data) (n bound : ℕ)
    (hcount : (d.stacks 260).length ≤ n + 1)
    (hframe : ∀ i, (d.stacks i).length ≤ bound)
    (prefixSteps : ℕ)
    (c : Cfg 80 1220 (size exportCount + 1))
    (ht : prefixSteps ≤ 2 * (d.stacks 0).length + 2 * (d.stacks 256).length +
      7 * (d.stacks 260).length + 12)
    (hc : Trace (compiled exportCount 256 256) prefixSteps
      (d.withPC (some (compiled exportCount 256 256).entry)) c) :
    dataBits c ≤ 1224 * bound + 7 * n + 19 := by
  have hsum : stackBits d.stacks ≤ 1220 * bound := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hframe i)
    simpa only [stackBits, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] using h
  have h0 := hframe 0
  have hout := hframe 256
  have hg := trace_dataBits (compiled exportCount 256 256) hc
  change dataBits c ≤ stackBits d.stacks + prefixSteps at hg
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete startup for the shared 80-register, 1220-stack DFS ABI.
The input frame already contains the normalized body and actual parameter words.
This module proves only startup; it does not assume or claim a completed DFS run.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

variable {n : ℕ}

theorem startFrontier_refinement (M : List Bool) (F : RawCNF n) (d : Data)
    (hp : Prepared M F d) :
    ∃ e, Eval startFrontier (8 * (SparseCountProgram.encodeBody F).length + 13) d e ∧
      e.stacks 265 = [] ∧
      e.stacks 257 = pendingBytes [⟨F, 0⟩] ∧
      (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) := by
  let a := SparseFrontierProgram.state (d.regs 0) (d.regs 1) (d.regs 2)
    (SparseCountProgram.encodeBody F) (Encoding.encodeNat n) [] []
  let b := SparseFrontierProgram.state true false (d.regs 2) [] (Encoding.encodeNat n)
    (Encoding.encodeList id [SparseCountProgram.encodeBody F]) []
  have hin : embedState (registers 3 (by decide)) frontierStack d a = d := by
    apply embedState_eq_of_ports _ _ d d a (registers 3 (by decide)).injective
      frontierStack.injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i
      · exact hp.current
      · exact hp.header
      · exact hp.pending
      · exact hp.low_empty 23 (by decide)
    · intro i hi
      rfl
  have he := eval_call_lifted SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack d (registers 3 (by decide)).injective
    frontierStack.injective
    (SparseFrontierProgram.initFrontier_trace (SparseCountProgram.encodeBody F)
      (Encoding.encodeNat n) (d.regs 0) (d.regs 1) (d.regs 2))
  change Eval startFrontier _ (embedState _ _ d a) (embedState _ _ d b) at he
  rw [hin] at he
  let e := embedState (registers 3 (by decide)) frontierStack d b
  have hout (i : Fin 4) : e.stacks (frontierStack i) = b.stacks i :=
    embedState_stack _ _ _ _ frontierStack.injective i
  refine ⟨e, he, hout 0, hout 2, ?_⟩
  intro i hc hpending
  by_cases hi : ∃ j, frontierStack j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · exact (hc rfl).elim
    · exact (hout 1).trans hp.header.symm
    · exact (hpending rfl).elim
    · exact (hout 3).trans (hp.low_empty 23 (by decide)).symm
  · exact embedState_stack_frame _ _ _ _ i hi

theorem startup_refinement (M : List Bool) (F : RawCNF n) (d : Data)
    (hp : Prepared M F d) :
    ∃ e, Eval startup (8 * (SparseCountProgram.encodeBody F).length + 16) d e ∧
      Boundary M ⟨[⟨F, 0⟩], 0⟩ e ∧
      (∀ i, i ≠ 257 → i ≠ 260 → i ≠ 265 → e.stacks i = d.stacks i) := by
  obtain ⟨a, ha, hacurrent, hapending, haframe⟩ := startFrontier_refinement M F d hp
  have hatotal : a.stacks 260 = [] := (haframe 260 (by decide) (by decide)).trans hp.total
  let b : Data := ⟨Function.update a.regs 0 false, Function.update a.stacks 260 [false]⟩
  have hb : Eval startTotal 2 a b := startTotal_eval a hatotal
  let e : Data := ⟨readRegs b.regs 2 1 (b.stacks 257).head?, b.stacks⟩
  have he : Eval testPending 1 b e := testPending_eval b
  have hframe (i : Fin 1220) (hi257 : i ≠ 257) (hi260 : i ≠ 260) (hi265 : i ≠ 265) :
      e.stacks i = d.stacks i := by
    change Function.update a.stacks 260 [false] i = d.stacks i
    rw [Function.update_of_ne hi260, haframe i hi265 hi257]
  refine ⟨e, ?_, ?_, hframe⟩
  · exact ha.seq (hb.seq he)
  · constructor
    · simpa only [e, b, Function.update_of_ne (by decide : (257 : Fin 1220) ≠ 260)]
        using hapending
    · exact (hframe 258 (by decide) (by decide) (by decide)).trans hp.header
    · exact (hframe 259 (by decide) (by decide) (by decide)).trans hp.threshold
    · rfl
    · exact (hframe 261 (by decide) (by decide) (by decide)).trans hp.left_empty
    · exact (hframe 262 (by decide) (by decide) (by decide)).trans hp.right_empty
    · exact (hframe 263 (by decide) (by decide) (by decide)).trans hp.leaf_empty
    · simpa only [e, b, Function.update_of_ne (by decide : (265 : Fin 1220) ≠ 260)]
        using hacurrent
    · intro i hi
      rw [hframe i (by intro h; subst i; omega) (by intro h; subst i; omega)
        (by intro h; subst i; omega)]
      exact hp.low_empty i hi
    · simp [e, b, hapending, pendingBytes, Encoding.encodeList, readRegs]

/-- Startup is polynomial-time, so its own local time bounds every source
prefix. This estimate is never applied to the exponentially long DFS loop. -/
theorem startup_prefix_space (d : Data) (bodyLength bound : ℕ)
    (hframe : ∀ i, (d.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 8 * bodyLength + 17 →
      Trace (compiled startup 256 256) prefixSteps
        (d.withPC (some (compiled startup 256 256).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ 1220 * bound + 8 * bodyLength + 17 := by
  have hsum : dataBits (d.withPC (some (compiled startup 256 256).entry)) ≤ 1220 * bound := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 1220))) => hframe i)
    simpa only [dataBits, stackBits, StructuredProgram.State.withPC, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  intro prefixSteps intermediate hle htrace i
  have h := StructuredSpace.local_stack_bound (compiled startup 256 256)
    (steps := 8 * bodyLength + 17) hsum prefixSteps intermediate hle htrace i
  simpa only [Nat.add_assoc] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem boundedEval_mono {code : Code} {t a b small large}
    (h : BoundedEval code t a b small) (hle : small ≤ large) : BoundedEval code t a b large :=
  ⟨h.eval, fun p c hp hc i => (h.space p c hp hc i).trans hle⟩

private theorem stack_length_le_dataBits {r s l : ℕ} (c : Cfg r s l) (i : Fin s) :
    (c.stacks i).length ≤ dataBits c :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((c.stacks j).length)) (Finset.mem_univ i)

/-- Startup, every real DFS visit, and the canonical count-word copy form one
actual source execution. The leaf is still an explicit finite-command contract
which the streamed evaluator must discharge before endpoint acceptance. -/
theorem command_execution_oai (k : ℕ) (threshold : List Bool) (leaf : Code)
    (F : RawCNF n) (d : Data) (leafTime inputBound bound : ℕ)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (prepared : DFSStartup.Prepared threshold (ExecCNF.normalize SAT.Literal.negate F) d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hinput : ∀ i, (d.stacks i).length ≤ inputBound)
    (hstartup : 1220 * inputBound +
      8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 17 ≤ bound)
    (hvisit : visitSpace k n F.length threshold.length ≤ bound)
    (hleaf : LeafContract (n := n) k threshold inputBound leaf leafTime bound) :
    ∃ visits t e,
      t ≤ 8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 16 +
        (visits * (visitTime k n (SparseCountProgram.formulaBound n k)
          threshold.length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
      BoundedEval (command k leaf) t d e (1224 * bound + 7 * n + 19) ∧
      e.stacks 256 = OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord (rawCount F) ∧
      Transitions k (BinaryArithmetic.toNat threshold) visits
        ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨[], rawCount F⟩ := by
  obtain ⟨a, heval, hboundary, hframe⟩ :=
    DFSStartup.startup_refinement threshold (ExecCNF.normalize SAT.Literal.negate F) d prepared
  have startEval : BoundedEval DFSStartup.startup
      (8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 16)
      d a bound := by
    refine ⟨heval, ?_⟩
    intro t c ht hc i
    exact (DFSStartup.startup_prefix_space d
      (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length
      inputBound hinput t c (by omega) hc i).trans hstartup
  have aDimension : BinaryArithmetic.toNat (a.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1) := by
    rw [hframe 264 (by decide) (by decide) (by decide)]
    exact hdimension
  have aAmbient : BinaryArithmetic.toNat (a.stacks 267) = n := by
    rw [hframe 267 (by decide) (by decide) (by decide)]
    exact hambient
  have aParameterLength : (a.stacks 264).length ≤ inputBound := by
    rw [hframe 264 (by decide) (by decide) (by decide)]
    exact hinput 264
  have aAmbientLength : (a.stacks 267).length ≤ n + 1 := by
    rw [hframe 267 (by decide) (by decide) (by decide)]
    exact hambientLength
  have constraints := hvisit
  dsimp [visitSpace] at constraints
  obtain ⟨visits, tl, b, htl, loopEval, finalBoundary, transitions⟩ :=
    DFSNative.normalized_loop k threshold leaf F a leafTime inputBound bound hk hM hwidth hboundary
      aDimension aAmbient aParameterLength aAmbientLength startEval.final_bound
      (by omega) (by omega) (by omega) (by omega) hleaf
  have lengthTotal : (b.stacks 260).length ≤ n + 1 := by
    rw [finalBoundary.total]
    exact binaryNat_length_le (rawCount_le F)
  have bBound := loopEval.final_bound
  obtain ⟨e, exportEval, hout, _, _⟩ := exportCount_eval b
  let exportTime := 2 * (b.stacks 0).length + 2 * (b.stacks 256).length +
    7 * (b.stacks 260).length + 11
  have exportBounded : BoundedEval exportCount exportTime b e (1224 * bound + 7 * n + 19) := by
    refine ⟨exportEval, ?_⟩
    intro t c ht hc i
    have htotal := exportCount_prefix_space b n bound lengthTotal bBound t c
      (by dsimp [exportTime] at ht; omega) hc
    exact (stack_length_le_dataBits c i).trans htotal
  have bound_le : bound ≤ 1224 * bound + 7 * n + 19 := by omega
  have whole := (boundedEval_mono startEval bound_le).seq ((boundedEval_mono loopEval bound_le).seq exportBounded)
  have hExportTime : exportTime ≤ 2 * bound + 7 * n + 18 := by
    have hz := finalBoundary.low_empty 0 (by decide)
    have hb256 := bBound 256
    dsimp [exportTime]
    rw [hz]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    omega
  refine ⟨visits, _, e, ?_, whole, ?_, transitions⟩
  · omega
  · rw [hout, finalBoundary.total, binaryNat_eq_countWord]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution_oai
