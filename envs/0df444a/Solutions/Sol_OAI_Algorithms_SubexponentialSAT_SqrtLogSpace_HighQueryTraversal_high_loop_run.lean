-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:55:08.074812+00:00
-- url     : https://prove2.me/submissions/733260cd-4ce0-4b25-b576-8d6763f595fa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_advance_resources

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

/-- All arithmetic is on payload bits; overflow contributes exactly one modulus. -/
theorem bumpWord_value (word : List Bool) :
    value (bumpWord word).2 + (if (bumpWord word).1 then 2 ^ word.length else 0) =
      value word + 1 := by
  induction word with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => simp [bumpWord, value]; omega
    | true =>
      cases h : (bumpWord bs).1 <;>
        simp [bumpWord, value, h, pow_succ] at * <;> omega

/-- Concatenation transports carry, independently of the frame representation. -/
theorem bumpWord_append (first second : List Bool) :
    bumpWord (first ++ second) =
      if (bumpWord first).1 then
        ((bumpWord second).1, (bumpWord first).2 ++ (bumpWord second).2)
      else (false, (bumpWord first).2 ++ second) := by
  induction first with
  | nil => simp [bumpWord]
  | cons b bs ih =>
    cases b with
    | false => simp [bumpWord]
    | true =>
      cases hc : (bumpWord bs).1 <;> simp [bumpWord, ih, hc]

/-- The tuple odometer is exactly fixed-width increment of all payload bits. -/
theorem bumpWords_flatten (words : List (List Bool)) :
    ((bumpWords words).1, (bumpWords words).2.flatten) = bumpWord words.flatten := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    have hf : (bumpWords words).1 = (bumpWord words.flatten).1 := congrArg Prod.fst ih
    have hs : (bumpWords words).2.flatten = (bumpWord words.flatten).2 := congrArg Prod.snd ih
    cases hc : (bumpWord word).1 <;>
      simp [bumpWords, hc, List.flatten_cons, bumpWord_append, hf, hs]

@[simp] theorem bumpWords_flatten_length (words : List (List Bool)) :
    (bumpWords words).2.flatten.length = words.flatten.length := by
  have hs : (bumpWords words).2.flatten = (bumpWord words.flatten).2 :=
    congrArg Prod.snd (bumpWords_flatten words)
  rw [hs, bumpWord_length]

theorem bumpWords_value (words : List (List Bool)) :
    value (bumpWords words).2.flatten +
        (if (bumpWords words).1 then 2 ^ words.flatten.length else 0) =
      value words.flatten + 1 := by
  have hf : (bumpWords words).1 = (bumpWord words.flatten).1 :=
    congrArg Prod.fst (bumpWords_flatten words)
  have hs : (bumpWords words).2.flatten = (bumpWord words.flatten).2 :=
    congrArg Prod.snd (bumpWords_flatten words)
  rw [hf, hs]
  exact bumpWord_value words.flatten

/-- Before the last bit-tuple, the counter advances by exactly one and does
not report overflow. This supports a rank argument for exhaustive traversal. -/
theorem advance_before_last (words : List (List Bool))
    (h : value words.flatten + 1 < 2 ^ words.flatten.length) :
    (bumpWords words).1 = false ∧ value (bumpWords words).2.flatten = value words.flatten + 1 := by
  have hv := bumpWords_value words
  cases hc : (bumpWords words).1 with
  | false =>
    refine ⟨rfl, ?_⟩
    simpa only [hc, Bool.false_eq_true, ite_false, add_zero] using hv
  | true =>
    have hv' : value (bumpWords words).2.flatten + 2 ^ words.flatten.length =
        value words.flatten + 1 := by simpa only [hc, ite_true, if_true] using hv
    omega

/-- The last bit-tuple resets all payload bits to value zero and reports
overflow. Record boundaries and every component width remain unchanged. -/
theorem overflow_at_last (words : List (List Bool))
    (h : value words.flatten + 1 = 2 ^ words.flatten.length) :
    (bumpWords words).1 = true ∧ value (bumpWords words).2.flatten = 0 := by
  have hv := bumpWords_value words
  have hb := value_lt_power_length (bumpWords words).2.flatten
  rw [bumpWords_flatten_length] at hb
  cases hc : (bumpWords words).1 with
  | false =>
    have hv' : value (bumpWords words).2.flatten = value words.flatten + 1 := by
      simpa only [hc, Bool.false_eq_true, ite_false, add_zero] using hv
    omega
  | true =>
    refine ⟨rfl, ?_⟩
    have hv' : value (bumpWords words).2.flatten + 2 ^ words.flatten.length =
        value words.flatten + 1 := by simpa only [hc, ite_true, if_true] using hv
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

theorem advanceResult_outside (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    CounterForPrograms.OutsideEq p d (advanceResult p d words) := by
  intro j hc hs
  change d.stacks j = (incrementResult p d words).stacks j
  exact (CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hs).symm

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

namespace NativeRound

theorem StageSpace.seq {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : StageSpace first n a bound) (hsecond : StageSpace second m b bound) :
    StageSpace (.seq first second) (n + m) a bound := by
  exact ⟨StructuredSpace.sequence_stack_bound hf hs 778 777 hfirst.bound hsecond.bound
    _ _ _ (compiled_site _ 778 777)⟩

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem sum_assignments_split {M : Type*} [AddCommMonoid M]
    (H : Finset V) (f : (V → Bool) → M) :
    ∑ x, f x = ∑ a : H → Bool, ∑ b : {v : V // v ∉ H} → Bool, f (glue H a b) := by
  calc
    _ = ∑ ab : (H → Bool) × ({v : V // v ∉ H} → Bool), f (glue H ab.1 ab.2) :=
      (Fintype.sum_equiv (assignmentEquiv H) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

theorem sum_by_rank {H M : Type*} [Fintype H] [DecidableEq H] [AddCommMonoid M] {h : ℕ}
    (order : Fin h ≃ H) (f : (H → Bool) → M) :
    ∑ a, f a = ∑ r : Fin (2 ^ h), f (highEquiv order r) := by
  exact (Fintype.sum_equiv (highEquiv order) _ _ (fun _ => rfl)).symm

/-- Every original assignment occurs once in the outer rank sum and inner
free-coordinate sum. This is the exact count bridge, including unused vars. -/
theorem sum_original_by_rank {V M : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid M] (H : Finset V) (order : Fin H.card ≃ H)
    (f : (V → Bool) → M) :
    ∑ x, f x = ∑ r : Fin (2 ^ H.card),
      ∑ b : {v : V // v ∉ H} → Bool, f (HighIncidence.glue H (highEquiv order r) b) := by
  rw [HighIncidence.sum_assignments_split H f]
  exact sum_by_rank order _

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Disjointness of the high-coordinate partition turns the native rank sum
into a full count over the original assignment space. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open scoped BigOperators

 theorem rankSum_eq_sum (value : ℕ → ℕ) (n : ℕ) :
    rankSum value 0 n = ∑ r : Fin n, value r.val := by
  rw [Fin.sum_univ_eq_sum_range, rankSum, ← List.range_eq_range']
  induction n with
  | zero => simp
  | succ n ih => simp [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem rankSum_original {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset V) (order : Fin H.card ≃ H) (P : (V → Bool) → Prop) [DecidablePred P]
    (value : ℕ → ℕ)
    (hvalue : ∀ r : Fin (2^H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (HighIncidence.glue H (HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0) :
    rankSum value 0 (2^H.card) = ∑ x : V → Bool, if P x then 1 else 0 := by
  rw [rankSum_eq_sum, HighIncidenceProgram.Rank.sum_original_by_rank H order]
  apply Finset.sum_congr rfl
  intro r _
  exact hvalue r

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem flattened_length (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) : words.flatten.length=H.card := by
  rw [List.length_flatten,hshape]
  simp

theorem physical_rank_lt (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) :
    CounterPrograms.value words.flatten < 2^H.card := by
  simpa only [flattened_length H words hshape] using
    ExecCNFTupleOdometer.value_lt_power_length words.flatten

theorem rankValue_at (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : Fin (2^H.card)) :
    rankValue H hashes marked clause r.val=NodeSemantics.ternaryFixedHighCount H
      (Rank.highEquiv (Order.highOrder H) r) hashes marked clause := by
  simp only [rankValue,dite_eq_left r.isLt]

theorem rankSum_fullCount (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    LeafBranchProgram.rankSum (rankValue H hashes marked clause) 0 (2^H.card)=
      fullCount hashes marked clause := by
  apply LeafBranchProgram.rankSum_original H (Order.highOrder H)
    (NodeSemantics.ternaryAccepted hashes marked clause)
  intro r
  exact rankValue_at H hashes marked clause r

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed high-counter loop. The induction index and prefix sum
are proof data only; executable syntax retains one bounded-width odometer and
one binary accumulator. The concrete per-rank stream proof is supplied by the
downstream count integration, not by a runtime callback. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount HighQueryLoop
open ExecCNFTupleEnumeration ExecCNFTupleOdometer
open HashGreedyProgram.NativeRound

/-- Prefix composition for a tested loop, before specializing its fixed body. -/
theorem while_step_space {body : Cmd 40 896} {test : Fin 40} {nb nt D : ℕ}
    {a b c : HighQueryAdapter.Data} (flag : a.regs test=true)
    (hb : Eval body nb a b) (ht : Eval (.while test body) nt b c)
    (sb : StageSpace body nb a D) (st : StageSpace (.while test body) nt b D) :
    StageSpace (.while test body) (nb+nt+1) a D :=
  ⟨StructuredSpace.while_true_stack_bound flag hb ht 778 777 sb.bound st.bound
    _ _ _ (compiled_site _ 778 777)⟩

/-- The final false guard does not allocate stack words. -/
theorem while_done_space (body : Cmd 40 896) (test : Fin 40) (D : ℕ)
    (a : HighQueryAdapter.Data) (flag : a.regs test=false)
    (bound : ∀ i,(a.stacks i).length≤D) : StageSpace (.while test body) 1 a D :=
  ⟨StructuredSpace.while_false_stack_bound body test a flag bound
    _ _ _ (compiled_site _ 778 777)⟩

/-- At overflow the fixed-width physical odometer returns its unique zero
tuple, including the empty tuple when the high set is empty. -/
theorem overflow_counter {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (shape : words.map List.length=List.replicate H.card 1)
    (last : CounterPrograms.value words.flatten+1=2^H.card) (a : HighQueryAdapter.Data) :
    (advanceResult highPorts.counter a words).stacks 789=
      Encoding.encodeList id (List.replicate H.card [false]) := by
  have hlast : CounterPrograms.value words.flatten+1=2^words.flatten.length := by
    rw [flattened_length H words shape]
    exact last
  have hz := (overflow_at_last words hlast).2
  have hzero : (bumpWords words).2=List.replicate H.card [false] := by
    apply tuple_eq_of_shape_value
    · simpa only [List.map_replicate,List.length_singleton] using
        (bumpWords_lengths words).trans shape
    · rw [hz]
      exact (zero_tuple_value H.card 1).symm
  change (advanceResult highPorts.counter a words).stacks highPorts.counter.counter=_
  rw [advanceResult_counter,hzero]

variable {n : ℕ} (H : Finset (Fin n))
  (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
  (clause : List (SAT.Literal (Fin n)))
  (I : HighQueryAdapter.Data → Prop) (B C D : ℕ)

/-- Direct induction over the remaining numerical ranks executes the fixed
branch and the real odometer, including the final overflow. Every boundary
returns the same B; intermediate prefixes use a separate uniform maximum.
The branch premise names the fixed actual command and remains explicit only
in this compositional support theorem. -/
theorem loop_run
    (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
    (width : 4*H.card+1≤B) (BD : B≤D)
    (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
      (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
      a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=
          rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤B) ∧
        StageSpace HighQueryProgram.branch steps a D)
    (fuel : ℕ) : ∀ (rank : ℕ) (words : List (List Bool)) (a : HighQueryAdapter.Data),
      words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] → a.stacks 791=[] →
      a.regs 21=true → CounterPrograms.value words.flatten=rank → rank+fuel=2^H.card →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval (loopCmd highPorts.counter HighQueryProgram.branch) steps a b ∧
        steps≤fuel*(C+28*H.card+12)+1 ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
        b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
        StageSpace (loopCmd highPorts.counter HighQueryProgram.branch) steps a
          (max D (40*(H.card+1))) := by
  induction fuel with
  | zero =>
    intro rank words a shape hi hc hs ht hf hv hremaining hacc hlen hb
    have hlt := physical_rank_lt H words shape
    omega
  | succ fuel ih =>
    intro rank words a shape hi hc hs ht hf hv hremaining hacc hlen hb
    have hr : rank<2^H.card := by omega
    obtain ⟨nb,b,he,hnb,hbi,hba,hbl,hbout,hbt,hbc,hbs,hbb,hbp⟩ :=
      branch rank hr words a shape hi hc hs ht hf hv hacc hlen hb
    have hbc' : b.stacks 789=Encoding.encodeList id words := hbc.trans hc
    have hbs' : b.stacks 790=[] := hbs.trans hs
    obtain ⟨na,hna,ha,hdb,hdp⟩ := advance_resources H words shape b B hbc' hbs' width hbb
    let next := advanceResult highPorts.counter b words
    have hoff := advanceResult_outside highPorts.counter b words
    have hdi : I next := stable 0 b next hoff hbi
    have hda : BinaryArithmetic.toNat (next.stacks 788)=
        rankSum (rankValue H hashes marked clause) 0 (rank+1) := by
      rw [←hoff 788 (by decide) (by decide)]
      exact hba
    have hdl : (next.stacks 788).length≤n+1 := by
      rw [←hoff 788 (by decide) (by decide)]
      exact hbl
    have hdo : next.stacks 323=[] := by
      rw [←hoff 323 (by decide) (by decide)]
      exact hbout
    have hdt : next.stacks 791=[] := by
      rw [←hoff 791 (by decide) (by decide)]
      exact hbt
    have hds : next.stacks 790=[] := advanceResult_scratch highPorts.counter b words
    have hbody := he.seq ha
    have hbp' : StageSpace HighQueryProgram.branch nb a (max D (40*(H.card+1))) :=
      ⟨fun k z hk hz i => (hbp.bound k z hk hz i).trans (Nat.le_max_left _ _)⟩
    have hdp' : StageSpace (advanceCmd highPorts.counter) na b (max D (40*(H.card+1))) := by
      constructor
      intro k z hk hz i
      exact (hdp.bound k z (hk.trans (Nat.le_succ _)) hz i).trans
        (max_le (Nat.le_max_right _ _) (BD.trans (Nat.le_max_left _ _)))
    have hbodySpace := StageSpace.seq he ha hbp' hdp'
    by_cases hz : fuel=0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten+1=2^words.flatten.length := by
        rw [flattened_length H words shape,hv]
        omega
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : next.regs 21=false := by
        change (advanceResult highPorts.counter b words).regs (highPorts.counter.register 2)=false
        rw [advanceResult_flag,hcarry]
        rfl
      have hdone : Eval (loopCmd highPorts.counter HighQueryProgram.branch) 1 next next :=
        .while_false hfalse
      have hdoneSpace : StageSpace (loopCmd highPorts.counter HighQueryProgram.branch) 1 next
          (max D (40*(H.card+1))) := by
        exact while_done_space _ _ _ next hfalse
          (fun i => (hdb i).trans (BD.trans (Nat.le_max_left _ _)))
      refine ⟨nb+na+1+1,next,.while_true hf hbody hdone,by omega,hdi,?_,hdl,hdo,hdt,?_,
        hds,hfalse,hdb,?_⟩
      · have heq : rank+1=2^H.card := by omega
        rw [heq,rankSum_fullCount] at hda
        exact hda
      · exact overflow_counter H words shape (by omega) b
      · exact while_step_space hf hbody hdone hbodySpace hdoneSpace
    · have hbefore : CounterPrograms.value words.flatten+1<2^words.flatten.length := by
        rw [flattened_length H words shape,hv]
        omega
      obtain ⟨hcarry,hvalue⟩ := advance_before_last words hbefore
      have htrue : next.regs 21=true := by
        change (advanceResult highPorts.counter b words).regs (highPorts.counter.register 2)=true
        rw [advanceResult_flag,hcarry]
        rfl
      have hshape := (bumpWords_lengths words).trans shape
      have hcounter : next.stacks 789=Encoding.encodeList id (bumpWords words).2 :=
        advanceResult_counter highPorts.counter b words
      obtain ⟨nt,c,heval,hnt,hci,hca,hcl,hco,hct,hcc,hcs,hcf,hcb,hcp⟩ :=
        ih (rank+1) (bumpWords words).2 next hshape hdi hcounter hds hdt htrue
          (by omega) (by omega) hda hdl hdb
      refine ⟨nb+na+nt+1,c,.while_true hf hbody heval,?_,hci,hca,hcl,hco,hct,hcc,hcs,hcf,hcb,?_⟩
      · rw [Nat.succ_mul]
        omega
      · exact while_step_space hf hbody heval hbodySpace hcp

/-- The real initializer, all high ranks, final overflow, false guard and
compiler halt are paid in one run. An empty high set still executes one
branch. The endpoint word bound is B, independently of the visit count. -/
theorem high_loop_run_oai
    (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
    (width : 4*H.card+1≤B) (BD : B≤D)
    (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
      (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
      a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=
          rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤B) ∧
        StageSpace HighQueryProgram.branch steps a D)
    (a : HighQueryAdapter.Data) (hi : I a)
    (hc : a.stacks 789=Encoding.encodeList id (List.replicate H.card [false]))
    (hs : a.stacks 790=[]) (ht : a.stacks 791=[])
    (hacc : BinaryArithmetic.toNat (a.stacks 788)=0)
    (hlen : (a.stacks 788).length≤n+1) (hb : ∀ i,(a.stacks i).length≤B) :
    ∃ steps b, Eval HighQueryProgram.highLoop steps a b ∧
      steps+1≤2^H.card*(C+28*H.card+12)+3 ∧ I b ∧
      BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
      (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
      b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        (a.withPC (some (compiled HighQueryProgram.highLoop 789 788).entry)) (b.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) a (max D (40*(H.card+1))) := by
  let started := startResult highPorts.counter a
  have hstart : Eval (startCmd highPorts.counter) 1 a started := .base (.atom _ _)
  have hi' : I started := stable 0 a started (fun _ _ _ => rfl) hi
  have shape : (List.replicate H.card [false]).map List.length=List.replicate H.card 1 := by simp
  have hz : CounterPrograms.value (List.replicate H.card [false]).flatten=0 :=
    zero_tuple_value H.card 1
  have hac : BinaryArithmetic.toNat (started.stacks 788)=
      rankSum (rankValue H hashes marked clause) 0 0 := by
    change BinaryArithmetic.toNat (a.stacks 788)=_
    simpa only [rankSum,List.range'_zero,List.map_nil,List.sum_nil] using hacc
  obtain ⟨nt,b,he,hnt,hbi,hba,hbl,hbo,hbt,hbc,hbs,hbf,hbb,hbp⟩ :=
    loop_run H hashes marked clause I B C D stable width BD branch (2^H.card)
      0 (List.replicate H.card [false]) started shape hi' hc hs ht
      (startResult_flag highPorts.counter a) hz (by omega) hac hlen hb
  have hwhole : Eval HighQueryProgram.highLoop (1+nt) a b := hstart.seq he
  have hstartSpace : StageSpace (startCmd highPorts.counter) 1 a (max D (40*(H.card+1))) := by
    constructor
    intro k z hk hz i
    have hk' : k=0 ∨ k=1 := by omega
    rcases hk' with rfl|rfl
    · cases hz
      exact (hb i).trans (BD.trans (Nat.le_max_left _ _))
    · rw [trace_same_length_unique hz (compiled_trace hstart 778 777)]
      exact (hb i).trans (BD.trans (Nat.le_max_left _ _))
  have hp := StageSpace.seq hstart he hstartSpace hbp
  refine ⟨1+nt,b,hwhole,by omega,hbi,hba,hbl,hbo,hbt,hbc,hbs,hbf,hbb,
    compiled_halt_trace hwhole 789 788,?_⟩
  -- the sequence is reached through an equation, so the kernel never unfolds the
  -- compiled `highLoop` table (comparing it with the unfolded one took a minute)
  have generic : ∀ {c first second : Cmd 40 896} {n m D : ℕ} {x mid y : HighQueryAdapter.Data},
      c = .seq first second → Eval first n x mid → Eval second m mid y →
      StageSpace (.seq first second) (n + m) x D → StageSpace c (n + m + 1) x D := by
    intro c first second n m D x mid y hceq hf hs sp
    subst hceq
    exact ⟨StructuredSpace.compiled_halt_stack_bound (hf.seq hs) 778 777 sp.bound⟩
  exact generic (c := HighQueryProgram.highLoop) rfl hstart he hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run_oai
