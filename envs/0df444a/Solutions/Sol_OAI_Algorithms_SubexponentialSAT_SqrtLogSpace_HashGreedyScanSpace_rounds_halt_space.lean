-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:29:53.520664+00:00
-- url     : https://prove2.me/submissions/a166bded-d342-49a8-9657-e48bf99ec3f7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyRound_scan_minimum
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace_scan_halt_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A binary-score minimum update implemented by finite bit programs

The score is a little-endian bit word. Comparisons inspect its numeric value,
not its length. Candidate payloads may themselves be binary indices or encoded
rows. Ports 0/1 hold the incoming payload/score, 2/3 the incumbent, 4--7 are
scratch, and 8 is an untouched caller queue. Every copy and comparison below
has a measured trace of a fixed finite instruction table.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem clear_eval (d : Data) (dst : Fin 9) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 2 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 9)
    (hsd : src ≠ dst) (hs : src ≠ 7) (hd : (7 : Fin 9) ≠ dst)
    (htmp : d.stacks 7 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 7 1 2 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem replace_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval replace (2 * (d.stacks 2).length + 7 * (d.stacks 0).length +
      2 * (d.stacks 3).length + 7 * (d.stacks 1).length + 16) d (afterReplace d) := by
  have h1 := clear_eval d 2
  have h2 := copy_eval (afterClear d 2) 0 2 (by decide) (by decide) (by decide)
    (by simpa [afterClear, clearStacks] using htmp)
  have h3 := clear_eval (afterCopy (afterClear d 2) 0 2) 3
  have h4 := copy_eval (afterClear (afterCopy (afterClear d 2) 0 2) 3) 1 3
    (by decide) (by decide) (by decide)
    (by simpa [afterClear, afterCopy, clearStacks, copyStacks] using htmp)
  convert Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)) using 1 <;>
    simp [ afterReplace, afterClear, afterCopy, clearStacks, copyStacks] ; omega

theorem cleanup_eval (d : Data) :
    Eval cleanup (2 * (d.stacks 0).length + 2 * (d.stacks 1).length +
      2 * (d.stacks 6).length + 9) d (afterCleanup d) := by
  convert Eval.seq (clear_eval d 0) (Eval.seq (clear_eval (afterClear d 0) 1)
    (clear_eval (afterClear (afterClear d 0) 1) 6)) using 1 <;>
    simp [ afterCleanup, afterClear, clearStacks] ; omega

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An executable finite argmin. Scores are natural numbers, not unary
word lengths. The companion trace records both score calls at every scan
step, including repeated calls and all losing candidates. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

variable {R : Type*}

theorem best_mem (score : R → ℕ) (seed : R) (rs : List R) :
    best score seed rs ∈ seed :: rs := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    by_cases hs : score r < score seed
    · simp only [hs, ↓reduceIte]
      exact List.mem_cons_of_mem seed (ih r)
    · simp only [hs, ↓reduceIte]
      rcases List.mem_cons.mp (ih seed) with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
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

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht


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

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

/-- A boundary invariant and a uniform actual-body prefix bound establish the
same space bound through any finite number of loop iterations. -/
theorem loop_stack_bound {r s : ℕ} (body : StructuredCalls.Cmd r s) (test : Fin r)
    (inputStack outputStack : Fin s) (I : StructuredCalls.State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → I b)
    (hbody : ∀ n a b, StructuredCalls.Eval body n a b → I a → a.regs test = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
          (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  induction steps using Nat.strong_induction_on generalizing a b with
  | h steps ih =>
      cases heval with
      | while_false htest =>
          exact while_false_stack_bound body test a htest (hinitial a ha)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)
      | @while_true _ _ n m a middle b htest hb hw =>
          have hmiddle := hpreserve n a middle hb ha htest
          exact while_true_stack_bound htest hb hw inputStack outputStack
            (hbody n a middle hb ha htest) (ih m (by omega) hw hmiddle)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- A singleton shape contains exactly the one physical payload word. -/
theorem tuple_eq_singleton_flatten {words : List (List Bool)} {width : ℕ}
    (hshape : words.map List.length = [width]) : words = [words.flatten] := by
  obtain ⟨word, rfl, _⟩ := List.map_eq_singleton_iff.mp hshape
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The streamed strict argmin and its greedy invariant. Candidate indices describe
an iterator's successive callbacks; no list of candidates is constructed here.
The finite-program implementation must refine these recurrences. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy

open OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect
open scoped BigOperators

variable {R X : Type*}


private theorem best_append (evaluate : R → ℕ) (seed : R) (xs ys : List R) :
    best evaluate seed (xs ++ ys) = best evaluate (best evaluate seed xs) ys := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- The native iterator's proof-only visit log agrees with the indexed scan.
The seed's repeated visit at index zero leaves its cached score unchanged. -/
theorem scan_eq_best (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).1 =
      best evaluate (candidate 0) ((List.range' 0 (t + 1)).map candidate) := by
  induction t with
  | zero => simp [scan, best]
  | succ t ih =>
    rw [List.range'_concat, List.map_append, best_append]
    simp only [Nat.one_mul, Nat.zero_add, List.map_cons, List.map_nil, best, ← ih]
    simp only [scan, update, scan_score]
    split_ifs <;> rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgminBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bootstrap the binary argmin from an empty incumbent. The initial candidate
load is paid explicitly, including the empty-input case. -/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem installFirst_eval (B C : ℕ) (next : Entry) (queue : List Bool)
    (regs : Fin 8 → Bool) (hn : Fits B C next) :
    ∃ n ≤ 100 * (B + C + 1), ∃ regs',
      Eval installFirst n (data regs next empty queue) (data regs' empty next queue) := by
  let d := data regs next empty queue
  have hr := replace_eval d (by rfl)
  have hc := cleanup_eval (afterReplace d)
  have hf : afterCleanup (afterReplace d) =
      data (afterCleanup (afterReplace d)).regs empty next queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ afterReplace, afterClear, afterCopy,
        StackRoutines.clearStacks, StackRoutines.copyStacks, d, data, store, empty]
  refine ⟨9 * next.payload.length + 9 * next.score.length + 25, ?_,
    (afterCleanup (afterReplace d)).regs, ?_⟩
  · rcases hn with ⟨hs, hp⟩
    omega
  · rw [← hf]
    convert Eval.seq hr hc using 1
    all_goals try with_reducible_and_instances rfl
    simp [afterReplace, afterClear, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks, d, data, store, empty]
    omega

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem readCounter_eval {r s : ℕ} (p : LoopPorts r s) (a : State r s) :
    Eval (readCounter p) 1 a (readCounterState p a) := .base (.atom _ _)

theorem iter_succ_apply {α : Type*} (next : α → α) (n : ℕ) (x : α) :
    iter next (n + 1) x = next (iter next n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [iter] using ih (next x)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

/-- Exact measured appending, with no retained candidate family. -/
theorem append_eval (a : State 8 10) :
    Eval appendWinner (5 * (a.stacks 2).length + 2 * (a.stacks 3).length + 10)
      a (appended a) := by
  let b := Subexp.TupleProgram.pushedState 9 0 false a
  let c := Subexp.TupleProgram.escapedState appendPorts b
  let d := Subexp.TupleProgram.pushedState 9 0 true c
  have h1 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) false a
  have h2 := Subexp.TupleProgram.escape_eval_state appendPorts b
  have h3 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) true c
  have h4 := Subexp.TupleProgram.clear_eval (3 : Fin 10) (0 : Fin 8) 1 d
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  · rfl
  · simp [b, c, d, appendPorts]
    omega
  · rfl

theorem appended_history (a : State 8 10) :
    (appended a).stacks 9 =
      true :: (Encoding.frame (a.stacks 2).reverse ++ a.stacks 9) := by
  simp [appended, StackRoutines.clearStacks, appendPorts, Subexp.TupleProgram.frame_eq_escaped,
    List.append_assoc]

theorem appended_frame (a : State 8 10) (i : Fin 10)
    (h2 : i ≠ 2) (h3 : i ≠ 3) (h9 : i ≠ 9) :
    (appended a).stacks i = a.stacks i := by
  simp [appended, StackRoutines.clearStacks, appendPorts, h2, h3, h9]

namespace NativeRound

private theorem projected_core (a : State 40 896) (hc : CoreClean a) :
    projectState registers coreStacks a = BinaryArgmin.data
      (fun i => a.regs (registers i)) (readEntry 768 769 a) (readEntry 770 771 a) [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  funext i
  fin_cases i <;> simp [coreStacks,
    BinaryArgmin.store, readEntry, hc.scratch772, hc.scratch773, hc.scratch774, hc.scratch775, hc.queue776]

private theorem embed_core_stacks (a : State 40 896) (hc : CoreClean a)
    (rf : Fin 8 → Bool) (winner : BinaryArgmin.Entry) :
    (embedState registers coreStacks a (BinaryArgmin.data rf BinaryArgmin.empty winner [])).stacks =
      stored a winner := by
  let d := projectState registers coreStacks a
  have hout : (BinaryArgmin.data rf BinaryArgmin.empty winner []).stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 winner.payload) 3 winner.score := by
    funext i
    fin_cases i <;> simp [d, projectState, coreStacks, BinaryArgmin.data,
      BinaryArgmin.store, BinaryArgmin.empty, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]
  have hs : Function.Injective coreStacks := core.stack_injective
  change Function.extend coreStacks _ a.stacks = _
  rw [hout, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs]
  have hf : Function.extend coreStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers coreStacks a
      core.register_injective core.stack_injective)
  rw [hf]
  rfl

/-- Bootstrap pays the first full score and stores it by actual copying. -/
theorem install_eval (a : State 40 896) (B C : ℕ) (hc : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hn : BinaryArgmin.Fits B C (readEntry 768 769 a)) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ b,
      Eval install n a b ∧
      b.stacks = stored a (readEntry 768 769 a) := by
  have hb : readEntry 770 771 a = BinaryArgmin.empty := by
    simp [readEntry, BinaryArgmin.empty, hbp, hbs]
  obtain ⟨n, hn', rf, he⟩ := BinaryArgmin.installFirst_eval B C
    (readEntry 768 769 a) [] (fun i => a.regs (registers i)) hn
  have ht := compiled_halt_trace he 8 2
  have hp := projected_core a hc
  rw [hb] at hp
  rw [← hp] at ht
  refine ⟨n + 1, by omega, _,
    eval_call_from_state _ registers coreStacks a
      core.register_injective core.stack_injective ht, ?_⟩
  exact embed_core_stacks a hc rf _

theorem stored_clean (a : State 40 896) (winner : BinaryArgmin.Entry)
    (hc : CoreClean a) (b : State 40 896) (hb : b.stacks = stored a winner) :
    CoreClean b ∧ b.stacks 768 = [] ∧ b.stacks 769 = [] ∧
      readEntry 770 771 b = winner := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [hb, stored, readEntry, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]

/-- Serialize precisely one attained winner and clear its cached score. -/
theorem append_eval (a : State 40 896) :
    ∃ b, Eval append (5 * (a.stacks 770).length + 2 * (a.stacks 771).length + 11) a b ∧
      b.stacks = appendedStacks a := by
  let d := projectState registers historyStacks a
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective historyStacks := by decide
  have he := HashGreedyProgram.append_eval d
  have ht := compiled_halt_trace he 2 9
  refine ⟨embedState registers historyStacks a (appended d),
    eval_call_from_state appendProgram registers historyStacks a hr hs ht, ?_⟩
  have hout : (appended d).stacks =
      Function.update (Function.update (Function.update d.stacks 2 []) 3 []) 9
        (true :: (Encoding.frame (d.stacks 2).reverse ++ d.stacks 9)) := by
    funext i
    by_cases h2 : i = 2
    · subst i
      simp
    by_cases h3 : i = 3
    · subst i
      simp
    by_cases h9 : i = 9
    · subst i
      simp [appended_history]
    simp only [Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h9, appended_frame d i h2 h3 h9]
  change Function.extend historyStacks _ a.stacks = _
  rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs]
  have hf : Function.extend historyStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers historyStacks a hr hs)
  rw [hf]
  rfl

theorem resetGuard_eval (a : State 40 896) : Eval resetGuard 1 a (guardSet a) :=
  .base (.atom _ _)

/-- Measured composition uses the actual execution of each fixed stage.
This is deliberately an intermediate trace lemma, not a closed query service. -/
theorem round_eval_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np : ℕ)
    (ha : Eval (attempt mass) na a b)
    (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e) :
    Eval (round mass) (na + (ni + (ns + (np + 1)))) a (guardSet e) :=
  ha.seq (hi.seq (hs.seq (hp.seq (resetGuard_eval e))))

theorem StageSpace.seq {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : StageSpace first n a bound) (hsecond : StageSpace second m b bound) :
    StageSpace (.seq first second) (n + m) a bound := by
  exact ⟨StructuredSpace.sequence_stack_bound hf hs 778 777 hfirst.bound hsecond.bound
    _ _ _ (compiled_site _ 778 777)⟩

theorem resetGuard_space (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) : StageSpace resetGuard 1 a bound := by
  constructor
  intro k c hk ht i
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · cases ht
    exact hb i
  · rw [trace_same_length_unique ht (compiled_trace (resetGuard_eval a) 778 777)]
    exact hb i

/-- Stage bounds combine by their common maximum. In particular the number
of streamed candidates never multiplies the retained-space bound. -/
theorem round_space_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np bound : ℕ)
    (ha : Eval (attempt mass) na a b) (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e)
    (sa : StageSpace (attempt mass) na a bound) (si : StageSpace install ni b bound)
    (ss : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c bound)
    (sp : StageSpace append np d bound) :
    StageSpace (round mass) (na + (ni + (ns + (np + 1)))) a bound := by
  have he : ∀ i, (e.stacks i).length ≤ bound :=
    sp.bound np _ le_rfl (compiled_trace hp 778 777)
  exact StageSpace.seq ha (hi.seq (hs.seq (hp.seq (resetGuard_eval e)))) sa
    (StageSpace.seq hi (hs.seq (hp.seq (resetGuard_eval e))) si
      (StageSpace.seq hs (hp.seq (resetGuard_eval e)) ss
        (StageSpace.seq hp (resetGuard_eval e) sp (resetGuard_space e bound he))))

/-- The actual final halt also obeys the same uniform source-prefix bound. -/
theorem round_halt_space_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np bound : ℕ)
    (ha : Eval (attempt mass) na a b) (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e)
    (sa : StageSpace (attempt mass) na a bound) (si : StageSpace install ni b bound)
    (ss : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c bound)
    (sp : StageSpace append np d bound) :
    StageSpace (round mass) (na + (ni + (ns + (np + 1))) + 1) a bound := by
  have he := round_eval_of_stages mass a b c d e na ni ns np ha hi hs hp
  have hb := round_space_of_stages mass a b c d e na ni ns np bound ha hi hs hp sa si ss sp
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hb.bound⟩

theorem readCounter_space (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    StageSpace (HashSelectProgram.readCounter outer) 1 a bound := by
  constructor
  intro k c hk ht i
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · cases ht
    exact hb i
  · rw [trace_same_length_unique ht
      (compiled_trace (HashSelectProgram.readCounter_eval outer a) 778 777)]
    by_cases hi : i = 781
    · subst i
      have := hb 781
      simp only [HashSelectProgram.readCounterState,
        outer, Function.update_self, List.length_tail]
      omega
    · simpa [StructuredProgram.State.withPC, HashSelectProgram.readCounterState,
        outer, hi] using hb i

theorem round_cost_le (attemptCost scoreWidth payloadWidth na ni ns np : ℕ)
    (ha : na ≤ attemptCost)
    (hi : ni ≤ 100 * (scoreWidth + payloadWidth + 1) + 1)
    (hs : ns ≤ 2 ^ payloadWidth *
      (attemptCost + 100 * (scoreWidth + payloadWidth + 1) + 1 +
        7 * (2 * payloadWidth + 3) + 5) + 2)
    (hp : np ≤ 5 * payloadWidth + 2 * scoreWidth + 11) :
    na + (ni + (ns + (np + 1))) ≤ roundBudget attemptCost scoreWidth payloadWidth := by
  unfold roundBudget
  omega

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete streamed greedy rounds. The query seam below consists of actual
executions of the fixed attempt command; it must be instantiated by the native
exact-query implementation before an endpoint theorem can use these results. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- One complete fixed native round: paid seed, all candidate visits, native
comparison, one attained winner append, and charged outer flag restoration.
The mathematical range in the conclusion records the trace; it is not stored. -/
theorem round_minimum (mass : Cmd 40 896) (a : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hcounter : a.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : a.stacks 779 = [])
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ roundBudget attemptCost B C, ∃ b : State 40 896, ∃ winner : BinaryArgmin.Entry,
      Eval (round mass) n a b ∧
      b.stacks = Function.update a.stacks 777
        (true :: (Encoding.frame winner.payload.reverse ++ a.stacks 777)) ∧
      b.regs 9 = true ∧ BinaryArgmin.Fits B C winner ∧
      (∃ j < 2 ^ C, winner = entry j) ∧
      (∀ j < 2 ^ C, BinaryArgmin.value winner ≤ BinaryArgmin.value (entry j)) ∧
      winner = HashSelect.best BinaryArgmin.value (entry 0)
        ((List.range' 0 (2 ^ C)).map entry) := by
  have hpositive : 0 < 2 ^ C := pow_pos (by decide) _
  obtain ⟨na, hna, first, hea, hfirst⟩ := hattempt [List.replicate C false] a
    (by simp) (fun _ _ _ _ _ => rfl) hcounter hscratch
  have hfirst' : first.stacks = Function.update (Function.update a.stacks 768
      (entry 0).payload) 769 (entry 0).score := by
    simpa [CounterPrograms.value] using hfirst
  have hcore' : CoreClean first := by
    constructor <;> simp [hfirst', hcore.scratch772, hcore.scratch773,
      hcore.scratch774, hcore.scratch775, hcore.queue776]
  have hentry : readEntry 768 769 first = entry 0 := by simp [readEntry, hfirst']
  obtain ⟨ni, hni, seed, hei, hseed⟩ := NativeRound.install_eval first B C hcore'
    (by simp [hfirst', hbp]) (by simp [hfirst', hbs]) (by simpa only [hentry] using hfit 0 hpositive)
  have hseed' : seed.stacks = stored first (entry 0) := by simpa only [hentry] using hseed
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      seed.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hseed', stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hseed', stored, h1]
    simp [hseed', stored, hfirst', h768, h769, h770, h771]
  have hs0 : seed.stacks 768 = [] := by simp [hseed', stored]
  have hs1 : seed.stacks 769 = [] := by simp [hseed', stored]
  have hsCore : CoreClean seed := by
    constructor
    · rw [hframe 772 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hframe 773 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hframe 774 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hframe 775 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hframe 776 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hsCounter : seed.stacks 778 = Encoding.encodeList id [List.replicate C false] := by
    simp [hseed', stored, hfirst', hcounter]
  have hsScratch : seed.stacks 779 = [] := by simp [hseed', stored, hfirst', hscratch]
  have hsEntry : readEntry 770 771 seed = entry 0 := by simp [readEntry, hseed', stored]
  obtain ⟨ns, hns, final, hes, hfinal, hfScratch, hfCounter, hmem, hmin, hbest⟩ :=
    scan_minimum mass seed B C attemptCost entry hs0 hs1 hsCore hsCounter hsScratch hsEntry hfit
      (fun words d hw hd hc hs => hattempt words d hw
        (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
          (hframe i h770 h771 h778 h779)) hc hs)
  obtain ⟨after, hep, hafter⟩ := NativeRound.append_eval final
  let winner := readEntry 770 771 final
  have hfinalFrame : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      final.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    exact (hfinal.frame i h770 h771 h778 h779).trans (hframe i h770 h771 h778 h779)
  have hp : 5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11 ≤
      5 * C + 2 * B + 11 := by
    have hfitFinal := hfinal.fits
    rcases hfitFinal with ⟨hs, hp⟩
    dsimp only [readEntry] at hs hp
    omega
  refine ⟨na + (ni + (ns + (5 * (final.stacks 770).length +
    2 * (final.stacks 771).length + 11 + 1))),
    round_cost_le attemptCost B C _ _ _ _ hna hni hns hp,
    guardSet after, winner, ?_, ?_, by simp [guardSet], hfinal.fits, hmem, hmin, hbest⟩
  · exact round_eval_of_stages mass a first seed final after na ni ns
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) hea hei hes hep
  · change after.stacks = _
    rw [hafter]
    funext i
    by_cases h770 : i = 770
    · subst i
      simp [appendedStacks, hbp]
    by_cases h771 : i = 771
    · subst i
      simp [appendedStacks, hbs]
    by_cases h777 : i = 777
    · subst i
      simp [appendedStacks, winner, readEntry,
        hfinalFrame 777 (by decide) (by decide) (by decide) (by decide)]
    by_cases h778 : i = 778
    · subst i
      simp [appendedStacks, hfCounter, hcounter]
    by_cases h779 : i = 779
    · subst i
      simp [appendedStacks, hfScratch, hscratch]
    simp [appendedStacks, h770, h771, h777,
      hfinalFrame i h770 h771 h778 h779]

theorem chosenEntry_eq_best (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    chosenEntry entry C rows = HashSelect.best BinaryArgmin.value (entry rows 0)
      ((List.range' 0 (2 ^ C)).map (entry rows)) := by
  have hp : 1 ≤ 2 ^ C := by have := pow_pos (by decide : 0 < (2 : ℕ)) C; omega
  simpa only [chosenEntry, Nat.sub_add_cancel hp] using
    HashGreedy.scan_eq_best BinaryArgmin.value (entry rows) (2 ^ C - 1)

theorem rowBoundary_read (base a : State 40 896) (rows : List (List Bool))
    (ha : RowBoundary base rows a) :
    RowBoundary base rows (HashSelectProgram.readCounterState outer a) := by
  constructor
  · intro i h777 h781
    simpa [HashSelectProgram.readCounterState, outer, h781] using ha.frame i h777 h781
  · simpa [HashSelectProgram.readCounterState, outer] using ha.history

theorem rowBoundary_round (base a b : State 40 896) (rows : List (List Bool))
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (ha : RowBoundary base rows a)
    (hb : b.stacks = Function.update a.stacks 777
      (true :: (Encoding.frame (chosenEntry entry C rows).payload.reverse ++ a.stacks 777))) :
    RowBoundary base (nextRows entry C rows) b := by
  constructor
  · intro i h777 h781
    simpa [hb, h777] using ha.frame i h777 h781
  · simp [hb, ha.history, encodedHistory, nextRows, Encoding.encodeList]

theorem chosenEntry_mem (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    ∃ j < 2 ^ C, chosenEntry entry C rows = entry rows j := by
  have hm := HashSelect.best_mem BinaryArgmin.value (entry rows 0)
    ((List.range' 0 (2 ^ C)).map (entry rows))
  rw [← chosenEntry_eq_best] at hm
  rcases List.mem_cons.mp hm with hzero | hrest
  · exact ⟨0, pow_pos (by decide) _, hzero⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hrest
    exact ⟨j, by simpa using hj, he.symm⟩

theorem chosenEntry_fits (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (B C : ℕ) (rows : List (List Bool))
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    BinaryArgmin.Fits B C (chosenEntry entry C rows) := by
  obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
  rw [he]
  exact hfit j hj

theorem iter_length (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (initial : List (List Bool)) (q : ℕ) :
    (HashSelectProgram.iter (nextRows entry C) q initial).length = initial.length + q := by
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    simp [nextRows, ih, Nat.add_assoc]

/-- The physical serialized history grows only by the selected bounded row.
The exponentially many losing payloads never contribute to this retained word. -/
theorem encodedHistory_iter_length_le
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (B C count : ℕ)
    (initial : List (List Bool))
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    ∀ q ≤ count,
      (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length ≤
        (encodedHistory initial).length + q * (2 * C + 2) := by
  intro q
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    intro hq
    have hi := ih (by omega)
    have hfitChosen := chosenEntry_fits entry B C
      (HashSelectProgram.iter (nextRows entry C) q initial)
      (hfit _ (by rw [iter_length]; omega))
    have hbytes := hfitChosen.2
    rw [HashSelectProgram.iter_succ_apply]
    have hlen : (encodedHistory (nextRows entry C
        (HashSelectProgram.iter (nextRows entry C) q initial))).length =
        (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length +
          2 * (chosenEntry entry C (HashSelectProgram.iter (nextRows entry C) q initial)).payload.length + 2 := by
      simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
      omega
    rw [hlen, Nat.succ_mul q (2 * C + 2)]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage for the actual streamed candidate scan. The attempt
premises describe executions and prefixes of the fixed preparation/query/padding
command; the complete query implementation must instantiate them. No bound in
this module uses the number of candidates as a space bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound

theorem boundary_stack_bound (base a : State 40 896) (B C L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounter : 2 * C + 3 ≤ L)
    (ha : Boundary base B C a) (hs : a.stacks 779 = [])
    (hc : (a.stacks 778).length = 2 * C + 3) :
    ∀ i, (a.stacks i).length ≤ L := by
  intro i
  by_cases h770 : i = 770
  · subst i
    exact ha.fits.2.trans hC
  by_cases h771 : i = 771
  · subst i
    exact ha.fits.1.le.trans hB
  by_cases h778 : i = 778
  · subst i
    exact hc.le.trans hcounter
  by_cases h779 : i = 779
  · subst i
    simp [hs]
  rw [ha.frame i h770 h771 h778 h779]
  exact hbase i

/-- The scan bound can be used directly as a stage inside the actual round. -/
theorem stage_space_of_halt_space {mass : Cmd 40 896} {steps bound : ℕ}
    {a : State 40 896}
    (h : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass))
      (steps + 1) a bound) :
    StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) steps a bound := by
  constructor
  intro k c hk ht i
  exact h.bound k c (by omega) ht i

private theorem stage_mono {command : Cmd 40 896} {steps x y : ℕ}
    {a : State 40 896} (h : StageSpace command steps a x) (hxy : x ≤ y) :
    StageSpace command steps a y := by
  constructor
  intro k c hk ht i
  exact (h.bound k c hk ht i).trans hxy

private theorem local_stage {command : Cmd 40 896} {steps budget L : ℕ}
    {a : State 40 896} (hsteps : steps ≤ budget)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    StageSpace command steps a (896 * L + budget) := by
  constructor
  intro k c hk ht i
  exact StructuredSpace.local_stack_bound (compiled command 778 777)
    (StreamResources.dataBits_le_mul _ hL) k c (hk.trans hsteps) ht i

private theorem stored_bound (a b : State 40 896) (B C L : ℕ)
    (hL : ∀ i, (a.stacks i).length ≤ L) (hB : B ≤ L) (hC : C ≤ L)
    (winner : BinaryArgmin.Entry) (hw : BinaryArgmin.Fits B C winner)
    (hb : b.stacks = stored a winner) : ∀ i, (b.stacks i).length ≤ L := by
  intro i
  by_cases h768 : i = 768
  · subst i
    simp [hb, stored]
  by_cases h769 : i = 769
  · subst i
    simp [hb, stored]
  by_cases h770 : i = 770
  · subst i
    simpa [hb, stored] using hw.2.trans hC
  by_cases h771 : i = 771
  · subst i
    simpa [hb, stored] using hw.1.le.trans hB
  simpa [hb, stored, h768, h769, h770, h771] using hL i

/-- The actual complete round uses the same fixed polynomial storage cap:
one seed attempt, native install, the uniform scan, native append, and the
charged guard reset. The entry cap includes all previously retained history. -/
theorem round_halt_space (mass : Cmd 40 896) (a : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hcounter : a.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : a.stacks 779 = [])
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ words d n b, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      (∀ i, (d.stacks i).length ≤ L) →
      Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
    {steps : ℕ} {b : State 40 896} (he : Eval (round mass) steps a b) :
    StageSpace (round mass) (steps + 1) a
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  let bound := max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)
  have hzero := hfit 0 (pow_pos (by decide) C)
  obtain ⟨na, _, first, hea, hfirst⟩ := hattempt [List.replicate C false] a
    (by simp) (fun _ _ _ _ _ => rfl) hcounter hscratch
  have hfirst' : first.stacks = Function.update (Function.update a.stacks 768
      (entry 0).payload) 769 (entry 0).score := by
    simpa [CounterPrograms.value] using hfirst
  have hfirstCore : CoreClean first := by
    constructor <;> simp [hfirst', hcore.scratch772, hcore.scratch773,
      hcore.scratch774, hcore.scratch775, hcore.queue776]
  have hfirstBound : ∀ i, (first.stacks i).length ≤ L := by
    intro i
    by_cases h768 : i = 768
    · subst i
      simpa [hfirst'] using hzero.2.trans hC
    by_cases h769 : i = 769
    · subst i
      simpa [hfirst'] using hzero.1.le.trans hB
    simpa [hfirst', h768, h769] using hL i
  have hentry : readEntry 768 769 first = entry 0 := by simp [readEntry, hfirst']
  obtain ⟨ni, hni, seed, hei, hseed⟩ := NativeRound.install_eval first B C hfirstCore
    (by simp [hfirst', hbp]) (by simp [hfirst', hbs])
    (by simpa only [hentry] using hzero)
  have hseed' : seed.stacks = stored first (entry 0) := by simpa only [hentry] using hseed
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      seed.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hseed', stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hseed', stored, h1]
    simp [hseed', stored, hfirst', h768, h769, h770, h771]
  obtain ⟨hseedCore, hs0, hs1, hseedEntry⟩ := stored_clean first (entry 0) hfirstCore seed hseed'
  have hseedBound := stored_bound first seed B C L hfirstBound hB hC (entry 0) hzero hseed'
  have hsCounter : seed.stacks 778 = Encoding.encodeList id [List.replicate C false] := by
    simp [hseed', stored, hfirst', hcounter]
  have hsScratch : seed.stacks 779 = [] := by simp [hseed', stored, hfirst', hscratch]
  have seedAttempt := fun words d hw (hd : Boundary seed B C d) hc hs =>
    hattempt words d hw
      (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
        (hframe i h770 h771 h778 h779)) hc hs
  obtain ⟨ns, _, final, hes, hfinal, hfScratch, hfCounter, _, _, _⟩ :=
    scan_minimum mass seed B C attemptCost entry hs0 hs1 hseedCore hsCounter hsScratch
      hseedEntry hfit seedAttempt
  have hscan := scan_halt_space mass seed B C L K attemptCost entry hs0 hs1 hseedCore
    hseedBound hB hC hcounterBound hsCounter hsScratch hseedEntry hfit seedAttempt
    (fun words d n b hw hd hc hs ht => hspace words d n b hw
      (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
        (hframe i h770 h771 h778 h779)) hc hs
      (boundary_stack_bound seed d B C L hseedBound hB hC hcounterBound hd hs (by
        have hlen : words.flatten.length = C := by
          have hh := congrArg List.sum hw
          simpa [List.length_flatten] using hh
        rw [hc, HashCandidateRank.tuple_eq_singleton_flatten hw]
        simp [Encoding.encodeList, Encoding.length_frame, hlen])) ht) hes
  have hfinalBound := boundary_stack_bound seed final B C L hseedBound hB hC hcounterBound
    hfinal hfScratch (by simp [hfCounter, Encoding.encodeList, Encoding.length_frame])
  obtain ⟨after, hep, _⟩ := NativeRound.append_eval final
  have happendCost : 5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11 ≤
      5 * C + 2 * B + 11 := by
    have hscore := hfinal.fits.1
    have hpayload := hfinal.fits.2
    dsimp only [readEntry] at hscore hpayload
    omega
  have hseedSpace : StageSpace (attempt mass) na a bound :=
    stage_mono (hspace [List.replicate C false] a na first (by simp)
      (fun _ _ _ _ _ => rfl) hcounter hscratch hL hea) (Nat.le_max_left _ _)
  have hinstallSpace : StageSpace install ni first bound := by
    apply stage_mono (local_stage hni hfirstBound)
    dsimp [bound]
    omega
  have happendSpace : StageSpace append
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) final bound := by
    apply stage_mono (local_stage happendCost hfinalBound)
    dsimp [bound]
    omega
  have hfull := round_halt_space_of_stages mass a first seed final after na ni ns
    (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) bound
    hea hei hes hep hseedSpace hinstallSpace (stage_space_of_halt_space hscan) happendSpace
  have hsteps := StreamResources.eval_steps_eq 778 777 he
    (round_eval_of_stages mass a first seed final after na ni ns
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) hea hei hes hep)
  rw [hsteps]
  exact hfull

private theorem row_boundary_core (base a : State 40 896) (rows : List (List Bool))
    (hc : CoreClean base) (ha : RowBoundary base rows a) : CoreClean a := by
  constructor
  · rw [ha.frame 772 (by decide) (by decide)]
    exact hc.scratch772
  · rw [ha.frame 773 (by decide) (by decide)]
    exact hc.scratch773
  · rw [ha.frame 774 (by decide) (by decide)]
    exact hc.scratch774
  · rw [ha.frame 775 (by decide) (by decide)]
    exact hc.scratch775
  · rw [ha.frame 776 (by decide) (by decide)]
    exact hc.queue776

private theorem read_credit (a : State 40 896) :
    ((HashSelectProgram.readCounterState outer a).stacks 781).length +
      (if (HashSelectProgram.readCounterState outer a).regs 9 then 1 else 0) =
        (a.stacks 781).length := by
  cases hw : a.stacks 781 <;>
    simp [HashSelectProgram.readCounterState, outer, readRegs, hw]

/-- All outer rounds retain only the attained history and a shrinking unary
counter. The history byte allowance is explicit and polynomial in the original
round count and row width; exponentially many losing rows are never retained. -/
theorem rounds_halt_space_oai (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = count)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hhistoryBound : (encodedHistory initial).length + count * (2 * C + 2) ≤ L)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = [])
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j))
    (hattempt : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry rows (CounterPrograms.value words.flatten)).payload) 769
          (entry rows (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d n b, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      (∀ i, (d.stacks i).length ≤ L) →
      Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
    {steps : ℕ} {b : State 40 896} (he : Eval (NativeRound.rounds mass) steps base b) :
    StageSpace (NativeRound.rounds mass) (steps + 1) base
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  let bound := max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)
  let rows := fun q => HashSelectProgram.iter (nextRows entry C) q initial
  let I := fun a : State 40 896 => ∃ q, q ≤ count ∧ RowBoundary base (rows q) a ∧
    q + (a.stacks 781).length + (if a.regs 9 then 1 else 0) = count
  have hcount : count ≤ L := by simpa only [hdepth] using hbase 781
  have hLb : L ≤ bound := by dsimp [bound]; omega
  have hrowBound : ∀ q a, q ≤ count → RowBoundary base (rows q) a →
      (a.stacks 781).length ≤ count → ∀ i, (a.stacks i).length ≤ L := by
    intro q a hq ha hcounterLength i
    by_cases h777 : i = 777
    · subst i
      rw [ha.history]
      have hh := encodedHistory_iter_length_le entry B C count initial hfit q hq
      have hm := Nat.mul_le_mul_right (2 * C + 2) hq
      exact hh.trans (by omega)
    by_cases h781 : i = 781
    · subst i
      exact hcounterLength.trans hcount
    rw [ha.frame i h777 h781]
    exact hbase i
  have hIbound : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound := by
    intro a hi i
    obtain ⟨q, hq, ha, hcredit⟩ := hi
    have hc : (a.stacks 781).length ≤ count := by omega
    exact (hrowBound q a hq ha hc i).trans hLb
  let iteration := Cmd.seq (round mass) (HashSelectProgram.readCounter outer)
  have hiteration : ∀ n a b, Eval iteration n a b → I a → a.regs 9 = true →
      I b ∧ StageSpace iteration n a bound := by
    intro n a b hab hi hflag
    obtain ⟨q, hq, ha, hcredit⟩ := hi
    have hcredit' : q + (a.stacks 781).length + 1 = count := by
      simpa only [hflag, ite_true, if_true] using hcredit
    have hq' : q < count := by omega
    have hlen : (rows q).length ≤ initial.length + count := by
      dsimp only [rows]
      rw [iter_length]
      omega
    have hreachable : ∃ j ≤ count, rows q = HashSelectProgram.iter (nextRows entry C) j initial :=
      ⟨q, hq, rfl⟩
    have hbytes : (encodedHistory (rows q)).length ≤
        (encodedHistory initial).length + count * (2 * C + 2) := by
      have hh := encodedHistory_iter_length_le entry B C count initial hfit q hq
      have hm := Nat.mul_le_mul_right (2 * C + 2) hq
      exact hh.trans (by omega)
    have haBound := hrowBound q a hq ha (by omega)
    have haCore := row_boundary_core base a (rows q) hcore ha
    have ha0 := (ha.frame 768 (by decide) (by decide)).trans h0
    have ha1 := (ha.frame 769 (by decide) (by decide)).trans h1
    have habp := (ha.frame 770 (by decide) (by decide)).trans hbp
    have habs := (ha.frame 771 (by decide) (by decide)).trans hbs
    have hacounter := (ha.frame 778 (by decide) (by decide)).trans hcounter
    have hascratch := (ha.frame 779 (by decide) (by decide)).trans hscratch
    dsimp only [iteration] at hab
    cases hab with
    | @seq _ _ nr nd a middle b hr hd =>
      obtain ⟨nt, _, last, winner, ht, hout, _, _, _, _, hbest⟩ :=
        round_minimum mass a B C attemptCost (entry (rows q)) ha0 ha1 haCore habp habs
          hacounter hascratch (hfit _ hlen) (hattempt _ a hlen ha hreachable hbytes)
      have hmid : middle.stacks = Function.update a.stacks 777
          (true :: (Encoding.frame (chosenEntry entry C (rows q)).payload.reverse ++
            a.stacks 777)) := by
        rw [hr.final_unique 778 ht, hout,
          hbest.trans (chosenEntry_eq_best entry C (rows q)).symm]
      have hmidRows : RowBoundary base (rows (q + 1)) middle := by
        have hh := rowBoundary_round base a middle (rows q) entry C ha hmid
        simpa only [rows, HashSelectProgram.iter_succ_apply] using hh
      have hmidCounter : middle.stacks 781 = a.stacks 781 := by simp [hmid]
      have hmidBound := hrowBound (q + 1) middle (by omega) hmidRows
        (by rw [hmidCounter]; omega)
      have hmidSpace := round_halt_space mass a B C L K attemptCost (entry (rows q))
        ha0 ha1 haCore habp habs haBound hB hC hcounterBound hacounter hascratch
        (hfit _ hlen) (hattempt _ a hlen ha hreachable hbytes) (hspace _ a hlen ha hreachable hbytes) hr
      have hroundSpace : StageSpace (round mass) nr a bound := by
        constructor
        intro k c hk hc i
        exact hmidSpace.bound k c (by omega) hc i
      have hb : b = HashSelectProgram.readCounterState outer middle :=
        hd.final_unique 778 (HashSelectProgram.readCounter_eval outer middle)
      have hnd : nd = 1 := StreamResources.eval_steps_eq 778 777 hd
        (HashSelectProgram.readCounter_eval outer middle)
      refine ⟨?_, ?_⟩
      · refine ⟨q + 1, by omega, ?_, ?_⟩
        · rw [hb]
          exact rowBoundary_read base middle (rows (q + 1)) hmidRows
        · rw [hb, Nat.add_assoc, read_credit, hmidCounter]
          omega
      · subst nd
        exact StageSpace.seq hr hd hroundSpace
          (readCounter_space middle bound (fun i => (hmidBound i).trans hLb))
  have hfull := he
  change Eval (.seq (HashSelectProgram.readCounter outer) (.while 9 iteration)) steps base b at he
  cases he with
  | @seq _ _ nr nl base middle b hr hl =>
    have hmiddle : middle = HashSelectProgram.readCounterState outer base :=
      hr.final_unique 778 (HashSelectProgram.readCounter_eval outer base)
    have hnr : nr = 1 := StreamResources.eval_steps_eq 778 777 hr
      (HashSelectProgram.readCounter_eval outer base)
    subst nr
    have hi : I middle := by
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · rw [hmiddle]
        apply rowBoundary_read base base initial
        exact ⟨fun _ _ _ => rfl, hhistory⟩
      · rw [hmiddle, Nat.zero_add, read_credit, hdepth]
    have hloop := StructuredSpace.loop_stack_bound iteration 9 778 777 I bound hIbound
      (fun n a b h hi hf => (hiteration n a b h hi hf).1)
      (fun n a b h hi hf => (hiteration n a b h hi hf).2.bound) hl hi
    have hwhole := StageSpace.seq hr hl
      (readCounter_space base bound (fun i => (hbase i).trans hLb)) ⟨hloop⟩
    exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hwhole.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space_oai
