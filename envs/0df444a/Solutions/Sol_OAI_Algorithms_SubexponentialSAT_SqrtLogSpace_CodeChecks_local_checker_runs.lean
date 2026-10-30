-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:03:40.212284+00:00
-- url     : https://prove2.me/submissions/6989e53d-de56-4e98-9422-bddf26cd690a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_wordCallback_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_rejection_scan_runs_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

open SubexpEnumerationPayload

theorem fieldWords_flatten {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).flatten = SubexpTupleRefinement.encodeTuple (scalarCode p) v := by
  simpa [fieldWords, SubexpTupleRefinement.tuplePayload, scalarCode] using
    SubexpTupleRefinement.tuplePayload_map (scalarCode p) v

/-- Each field vector has one unique counter state. -/
theorem fieldWords_injective {p d : ℕ} [Fact p.Prime] :
    Function.Injective (fieldWords (p := p) (d := d)) := by
  intro v w h
  apply SubexpTupleRefinement.encodeTuple_injective (scalarCode p) d
  simpa only [fieldWords_flatten] using congrArg List.flatten h

/-- Rejecting binary digit 3 leaves precisely the original ternary alphabet. -/
theorem ternary_digit_sound (x : Bool × Bool) (hx : invalidDigit true x = false) :
    ∃ a : ZMod 3, digitBits x = scalarBits a := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b
  · exact ⟨0, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · exact ⟨2, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · exact ⟨1, by
      unfold scalarBits
      have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx


theorem ternary_digit_complete (x : Bool × Bool) (a : ZMod 3)
    (ha : digitBits x = scalarBits a) : invalidDigit true x = false := by
  have hw : scalarWidth 3 = 2 := by norm_num [scalarWidth]
  unfold scalarBits at ha
  rw [hw] at ha
  rcases x with ⟨b,c⟩
  cases b <;> cases c <;> simp [invalidDigit]
  all_goals
    simp [digitBits, SubexpLiftRing.fixedBits] at ha
    have hval := a.val_lt
    omega


/-- Any width-two odometer state is exactly a list of scalar bit pairs. -/
theorem pairs_of_shape (words : List (List Bool)) (d : ℕ)
    (hshape : words.map List.length = List.replicate d 2) :
    ∃ xs : List (Bool × Bool), xs.length = d ∧ xs.map digitBits = words := by
  induction words generalizing d with
  | nil =>
    have hd : d = 0 := by simpa using congrArg List.length hshape.symm
    subst d
    exact ⟨[], rfl, rfl⟩
  | cons word words ih =>
    cases d with
    | zero => simp at hshape
    | succ d =>
      obtain ⟨hw, ht⟩ : word.length = 2 ∧ words.map List.length = List.replicate d 2 := by
        simpa [List.replicate_succ] using hshape
      obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hw
      obtain ⟨xs, hlen, hxs⟩ := ih d ht
      exact ⟨(a,b) :: xs, by simp [hlen], by simp [digitBits, hxs]⟩

private theorem digits_sound {p : ℕ} [Fact p.Prime] (xs : List (Bool × Bool))
    (h : ∀ x ∈ xs, ∃ a : ZMod p, digitBits x = scalarBits a) :
    ∃ v : Fin xs.length → ZMod p, xs.map digitBits = fieldWords v := by
  induction xs with
  | nil => exact ⟨Fin.elim0, rfl⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := h x (by simp)
    obtain ⟨v, hv⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨Fin.cons a v, ?_⟩
    simpa [fieldWords, List.ofFn_succ, ha] using congrArg (List.cons (scalarBits a)) hv

theorem ternary_digits_sound (xs : List (Bool × Bool))
    (hvalid : xs.any (invalidDigit true) = false) :
    ∃ v : Fin xs.length → ZMod 3, xs.map digitBits = fieldWords v := by
  apply digits_sound
  intro x hx
  apply ternary_digit_sound
  have h := List.any_eq_false.mp hvalid x hx
  exact Bool.eq_false_iff.mpr h


/-- Every actual ternary field vector passes the physical digit guard. -/
theorem ternary_field_valid (xs : List (Bool × Bool)) (v : Fin xs.length → ZMod 3)
    (h : xs.map digitBits = fieldWords v) : xs.any (invalidDigit true) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : digitBits x ∈ fieldWords v := h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [ternary_digit_complete x (v i) hi.symm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
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

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Enumerators
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

open BitProgram StructuredCalls ExecCNFTupleEnumeration

/-- The complete current tuple, including record delimiters, stays polynomial.
This is a bound on one word of data, not on the number of enumerated tuples. -/
theorem encoded_shape_length {words : List (List Bool)} {shape : List ℕ}
    (hshape : words.map List.length = shape) :
    (Encoding.encodeList id words).length = 2 * shape.sum + 2 * shape.length + 1 := by
  have hn := congrArg List.length hshape
  have hb := congrArg List.sum hshape
  simp only [List.length_map] at hn
  rw [ExecCNFTupleOdometer.encoded_length, hn]
  simpa only [List.length_flatten] using congrArg (fun n => 2 * n + 2 * shape.length + 1) hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

private theorem initialize_round (bit : Bool) (input output : List Bool)
    (regs : Fin 4 → Bool) (hzero : regs 0 = false) (hone : regs 1 = true) :
    Trace zeroTupleProgram 8 (initializeCfg (some 3) regs (bit :: input) output)
      (initializeCfg (some 3) (readRegs regs 2 3 (some bit)) input
        (true :: true :: false :: true :: false :: false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
    readRegs, Function.update_apply, hzero, hone]
  all_goals (funext i; fin_cases i <;> simp)

private theorem initialize_loop (input output : List Bool) (regs : Fin 4 → Bool)
    (hzero : regs 0 = false) (hone : regs 1 = true) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 3)
      (initializeCfg (some 3) regs input output)
      (initializeCfg none rf []
        ((List.replicate input.length [true, true, false, true, false, false]).flatten ++ output)) := by
  induction input generalizing regs output with
  | nil =>
      refine ⟨readRegs regs 2 3 none, ?_⟩
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
        readRegs, Function.update_apply]
  | cons bit input ih =>
      obtain ⟨rf, hr⟩ := ih
        (true :: true :: false :: true :: false :: false :: output)
        (readRegs regs 2 3 (some bit))
        (by simpa [readRegs] using hzero) (by simpa [readRegs] using hone)
      refine ⟨rf, ?_⟩
      have h := (initialize_round bit input output regs hzero hone).trans hr
      simpa [List.length_cons, List.replicate_succ', List.flatten_append,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

private theorem initialize_encoding (d : ℕ) :
    (List.replicate d [true, true, false, true, false, false]).flatten ++ [false] =
      Encoding.encodeList id (List.replicate d [false, false]) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simpa [List.replicate_succ, Encoding.encodeList, Encoding.frame] using
        congrArg (fun rest => true :: true :: false :: true :: false :: false :: rest) ih

/-- Empty dimensions produce the one-bit empty tuple, not an absent witness. -/
theorem initialize_trace (input : List Bool) (regs : Fin 4 → Bool) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 6)
      (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg none rf []
        (Encoding.encodeList id (List.replicate input.length [false, false]))) := by
  let ready := Function.update (Function.update regs 0 false) 1 true
  have hstart : Trace zeroTupleProgram 3 (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg (some 3) ready input [false]) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr, ready]
    first | done | (funext i; fin_cases i <;> rfl)
  obtain ⟨rf, hr⟩ := initialize_loop input [false] ready (by simp [ready]) (by simp [ready])
  refine ⟨rf, ?_⟩
  have h := hstart.trans hr
  have htime : 3 + (8 * input.length + 3) = 8 * input.length + 6 := by omega
  rw [htime] at h
  simpa [initialize_encoding] using h

/-- The dimension is consumed from one caller port; all other caller tapes
survive the concrete constructor call. -/
theorem initialize_call {R S : ℕ} (register : Fin 4 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (a : StructuredCalls.State R S) (houtput : a.stacks (stack 1) = []) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram zeroTupleProgram register stack))
        (8 * (a.stacks (stack 0)).length + 6) a b ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = Encoding.encodeList id
        (List.replicate (a.stacks (stack 0)).length [false, false]) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, ht⟩ := initialize_trace (a.stacks (stack 0)) (a.regs ∘ register)
  let final : StructuredCalls.State 4 2 :=
    ⟨rf, ![[], Encoding.encodeList id
      (List.replicate (a.stacks (stack 0)).length [false, false])]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC
      (some zeroTupleProgram.entry) =
      initializeCfg (some zeroTupleProgram.entry) (a.regs ∘ register)
        (a.stacks (stack 0)) [] := by
    change (⟨some zeroTupleProgram.entry, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 4 2 12) = _
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact houtput
  have ht' : Trace zeroTupleProgram (8 * (a.stacks (stack 0)).length + 6)
      ((StructuredCalls.projectState register stack a).withPC (some zeroTupleProgram.entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state zeroTupleProgram register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_⟩
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

private theorem convert_read (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 7
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 8) ![false, true, a, b, regs 4] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

private theorem convert_write (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 9
      (cfg (some 8) ![false, true, a, b, regs 4] input output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) := by
  cases ternary <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, convert, cfg, roundRegs, invalidDigit,
      execInstr, readRegs, Function.update_apply] <;>
    all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

private theorem convert_round (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 16
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) :=
  (convert_read ternary a b regs input output).trans
    (convert_write ternary a b regs input output)

private theorem convert_exit (ternary : Bool) (regs : Fin 5 → Bool) (output : List Bool) :
    Trace (convert ternary) 3
      (cfg (some 1) regs [false] output)
      (cfg none (readRegs regs 0 1 (some false)) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

private theorem convert_loop (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = (regs 4 || xs.any (invalidDigit ternary)) ∧
      Trace (convert ternary) (16 * xs.length + 3)
        (cfg (some 1) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  induction xs generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 (some false), ?_, ?_⟩
    · simp [readRegs]
    · simpa [tupleBits, scalarFrames, Encoding.encodeList] using convert_exit ternary regs output
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    obtain ⟨rf, hr, ht⟩ := ih (roundRegs ternary regs a b)
      (false :: b :: true :: a :: true :: output)
    refine ⟨rf, ?_, ?_⟩
    · simpa [roundRegs, Bool.or_assoc] using hr
    · have h := (convert_round ternary a b regs (tupleBits xs) output).trans ht
      simpa [tupleBits, scalarFrames, Encoding.encodeList, Encoding.frame, digitBits,
        Function.comp_def, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.append_assoc] using h

/-- Complete execution, including initialization, every rejected digit and halt. -/
theorem convert_trace (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = xs.any (invalidDigit ternary) ∧
      Trace (convert ternary) (16 * xs.length + 4)
        (cfg (some 0) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  obtain ⟨rf, hr, ht⟩ := convert_loop ternary xs (Function.update regs 4 false) output
  refine ⟨rf, by simpa using hr, ?_⟩
  have hstart : step (convert ternary) (cfg (some 0) regs (tupleBits xs) output) =
      some (cfg (some 1) (Function.update regs 4 false) (tupleBits xs) output) := by
    simp [step, convert, cfg, execInstr]
  have h := Computation.Trace.cons hstart ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl

/-- Concrete port relocation, preserving the entire off-port caller frame. -/
theorem convert_call {R S : ℕ} (ternary : Bool)
    (register : Fin 5 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (xs : List (Bool × Bool)) (a : StructuredCalls.State R S)
    (hinput : a.stacks (stack 0) = tupleBits xs) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram (convert ternary) register stack))
        (16 * xs.length + 4) a b ∧
      b.regs (register 4) = xs.any (invalidDigit ternary) ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = (scalarFrames xs).reverse ++ a.stacks (stack 1) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, hr, ht⟩ := convert_trace ternary xs (a.regs ∘ register) (a.stacks (stack 1))
  let final : StructuredCalls.State 5 2 :=
    ⟨rf, ![[], (scalarFrames xs).reverse ++ a.stacks (stack 1)]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry) =
      cfg (some 0) (a.regs ∘ register) (tupleBits xs) (a.stacks (stack 1)) := by
    change (⟨some 0, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 5 2 18) = _
    congr 1
    funext i
    fin_cases i
    · exact hinput
    · rfl
  have ht' : Trace (convert ternary) (16 * xs.length + 4)
      ((StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state (convert ternary) register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_, ?_⟩
  · exact (StructuredCalls.embedState_register _ _ _ _ register.injective 4).trans hr
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

/-- Preparing one streaming scan restores the dimension copy and scratch;
only the counter and the one-bit rejection latch are initialized. -/
theorem prepareScan_eval {S : ℕ} (p : ScanPorts S) (a : StructuredCalls.State 16 S)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = []) :
    ∃ b, StructuredCalls.Eval (prepareScan p) (15 * (a.stacks (p.stack 0)).length + 13) a b ∧
      b.stacks = Function.update
        (Function.update a.stacks (p.stack 2)
          (Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false])))
        (p.stack 4) [false] := by
  let copied : StructuredCalls.State 16 S :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (p.stack 0) (p.stack 1) a.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram (p.stack 0) (p.stack 1) (p.stack 3) 0 1))
      (7 * (a.stacks (p.stack 0)).length + 5) a copied :=
    .call _ (ListRegisterProgram.copy_run _ _ _ _ _
      (p.stack.injective.ne (by decide)) (p.stack.injective.ne (by decide))
      (p.stack.injective.ne (by decide)) (by decide) a.regs a.stacks hs)
  have hcopied : copied.stacks (p.stack 1) = a.stacks (p.stack 0) := by
    simp [copied, StackRoutines.copyStacks, hi]
  have hcopiedFrame (i : Fin S) (hne : i ≠ p.stack 1) : copied.stacks i = a.stacks i := by
    simp [copied, StackRoutines.copyStacks, hne]
  have houtput : copied.stacks ((scanInitializePorts p) 1) = [] := by
    change copied.stacks (p.stack 2) = []
    exact (hcopiedFrame _ (p.stack.injective.ne (by decide))).trans hc
  obtain ⟨initialized, hinitialize, hempty, htuple, hframe, _⟩ :=
    initialize_call scanRegisters (scanInitializePorts p) copied houtput
  have hinitInput : initialized.stacks (p.stack 1) = [] := hempty
  have hinitCounter : initialized.stacks (p.stack 2) =
      Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false]) := by
    change initialized.stacks (p.stack 2) = Encoding.encodeList id
      (List.replicate (copied.stacks (p.stack 1)).length [false, false]) at htuple
    simpa only [hcopied] using htuple
  have hinitFrame (i : Fin S) (h1 : i ≠ p.stack 1) (h2 : i ≠ p.stack 2) :
      initialized.stacks i = a.stacks i := by
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · exact h1 hj.symm
      · exact h2 hj.symm)]
    exact hcopiedFrame i h1
  let flagged := (StructuredProgram.Atom.set (s := S) 13 false).eval initialized
  let b := (StructuredProgram.Atom.push (p.stack 4) (13 : Fin 16)).eval flagged
  have hseed : StructuredCalls.Eval
      (.seq (.base (.atom (.set 13 false))) (.base (.atom (.push (p.stack 4) 13))))
      2 initialized b := .seq (.base (.atom _ _)) (.base (.atom _ _))
  refine ⟨b, ?_, ?_⟩
  · have h := hcopy.seq (hinitialize.seq hseed)
    change StructuredCalls.Eval (prepareScan p)
      ((7 * (a.stacks (p.stack 0)).length + 5) +
        ((8 * (copied.stacks (p.stack 1)).length + 6) + 2)) a b at h
    rw [hcopied] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · have hlatch : initialized.stacks (p.stack 4) = [] :=
      (hinitFrame _ (p.stack.injective.ne (by decide))
        (p.stack.injective.ne (by decide))).trans hl
    have hb : b.stacks = Function.update initialized.stacks (p.stack 4) [false] := by
      simp [b, flagged, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, hlatch]
    rw [hb]
    funext i
    by_cases h4 : i = p.stack 4
    · subst i; simp
    by_cases h2 : i = p.stack 2
    · subst i; simp [h4, hinitCounter]
    by_cases h1 : i = p.stack 1
    · subst i; simp [h4, h2, hinitInput, hi]
    · simp [h4, h2, hinitFrame i h1 h2]

theorem finishScan_eval {S : ℕ} (counter latch : Fin S) (hcl : counter ≠ latch)
    (a : StructuredCalls.State 16 S) (rejected : Bool) (hl : a.stacks latch = [rejected]) :
    ∃ b, StructuredCalls.Eval (finishScan counter latch)
      (2 * (a.stacks counter).length + 5) a b ∧ b.regs 15 = !rejected ∧
      b.stacks = Function.update (Function.update a.stacks latch []) counter [] := by
  let popped := (StructuredProgram.Atom.pop latch (13 : Fin 16) 14).eval a
  let flagged := (StructuredProgram.Atom.bnot (s := S) (15 : Fin 16) 13).eval popped
  let b : StructuredCalls.State 16 S :=
    ⟨readRegs flagged.regs 0 1 none, StackRoutines.clearStacks counter flagged.stacks⟩
  have hcounter : flagged.stacks counter = a.stacks counter := by
    simp [flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hcl]
  have hclear : StructuredCalls.Eval (.call (StackRoutines.clearProgram counter 0 1))
      (2 * (flagged.stacks counter).length + 3) flagged b :=
    .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  refine ⟨b, ?_, ?_, ?_⟩
  · have h := (StructuredCalls.Eval.base (.atom (.pop latch 13 14) a)).seq
      ((StructuredCalls.Eval.base (.atom (.bnot 15 13) popped)).seq hclear)
    rw [hcounter] at h
    convert h using 1
    · rfl
    · omega
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hl]
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      StackRoutines.clearStacks, hl]

/-- The native setup, complete core scan, actual Boolean readout and cleanup
form one measured run. Its storage uses the core's prefix bound, never the
core's possibly exponential running time. -/
theorem scanWrapper_resources {S l A B T : ℕ} (p : ScanPorts S) (core : Program 16 S l)
    (a : StructuredCalls.State 16 S) (rejected : Bool)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = [])
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcore : ∀ prepared : StructuredCalls.State 16 S,
      prepared.stacks = scanPreparedStacks p a →
      ∃ (n : ℕ) (middle : StructuredCalls.State 16 S), n ≤ T ∧
        Trace core n (prepared.withPC (some core.entry)) (middle.withPC none) ∧
        middle.stacks (p.stack 4) = [rejected] ∧
        (∀ i, i ≠ p.stack 2 → i ≠ p.stack 4 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace core prefixSteps (prepared.withPC (some core.entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ B) :
    ∃ steps out, StructuredCalls.Eval (scanWrapper p core) steps a out ∧
      steps ≤ T + 15 * (a.stacks (p.stack 0)).length + 2 * B + 18 ∧
      out.regs 15 = !rejected ∧ out.stacks = a.stacks ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (scanWrapper p core) (p.stack 0) (p.stack 4)).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18 := by
  obtain ⟨prepared, hprepare, hprepared⟩ := prepareScan_eval p a hi hc hs hl
  obtain ⟨n, middle, hn, htrace, hlatch, hframe, hspace⟩ := hcore prepared hprepared
  have hmiddle : ∀ i, (middle.stacks i).length ≤ B :=
    hspace n _ (Nat.le_refl _) htrace
  obtain ⟨out, hfinish, hanswer, hout⟩ := finishScan_eval (p.stack 2) (p.stack 4)
    (p.stack.injective.ne (by decide)) middle rejected hlatch
  have hcall : StructuredCalls.Eval (.call core) n prepared middle := .call _ htrace
  let bound := S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18
  have hprepareSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 15 * (a.stacks (p.stack 0)).length + 13 →
      Trace (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
        prefixSteps (a.withPC (some (StructuredCalls.compiled
          (prepareScan p) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (a.withPC (some (StructuredCalls.compiled
        (prepareScan p) (p.stack 0) (p.stack 4)).entry)) ≤ S * A :=
      StreamResources.dataBits_le_mul _ ha
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
      (steps := 15 * (a.stacks (p.stack 0)).length + 13) hinit prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hcallSpace : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4)) prefixSteps
        (prepared.withPC (some (StructuredCalls.compiled
          (.call core) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    have h := StructuredSpace.call_stack_bound core
      (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.call core)) (StructuredCalls.exitAddress (.call core))
      (fun pc => StructuredCalls.compiled_site (.call core) (p.stack 0) (p.stack 4) pc)
      htrace hspace
    intro prefixSteps intermediate hle ht i
    have hb := h prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hfinishSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 2 * (middle.stacks (p.stack 2)).length + 5 →
      Trace (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
        prefixSteps (middle.withPC (some (StructuredCalls.compiled
          (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (middle.withPC (some (StructuredCalls.compiled
        (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) ≤ S * B :=
      StreamResources.dataBits_le_mul _ hmiddle
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
      (steps := 2 * B + 5) hinit prefixSteps intermediate (by have := hmiddle (p.stack 2); omega) ht i
    dsimp [bound]
    omega
  refine ⟨(15 * (a.stacks (p.stack 0)).length + 13) +
    (n + (2 * (middle.stacks (p.stack 2)).length + 5)), out,
    hprepare.seq (hcall.seq hfinish), ?_, hanswer, ?_, ?_⟩
  · have := hmiddle (p.stack 2)
    omega
  · rw [hout]
    funext i
    by_cases h2 : i = p.stack 2
    · subst i; simp [hc]
    by_cases h4 : i = p.stack 4
    · subst i; simp [h2, hl]
    simp only [Function.update_of_ne h2, Function.update_of_ne h4]
    rw [hframe i h2 h4, hprepared]
    simp [h2, h4]
  · have hseq := StructuredSpace.sequence_stack_bound hcall hfinish (p.stack 0) (p.stack 4)
      hcallSpace hfinishSpace
      (StructuredCalls.compiled (.seq (.call core) (finishScan (p.stack 2) (p.stack 4)))
        (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.exitAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))
    exact StructuredSpace.sequence_stack_bound hprepare (hcall.seq hfinish) (p.stack 0) (p.stack 4)
      hprepareSpace hseq
      (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (scanWrapper p core))
      (StructuredCalls.exitAddress (scanWrapper p core))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramRepresentation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-for-byte agreement between generated candidates and arithmetic inputs.
These identities remove recoding from the search interface; they are not
assumptions that a rearrangement of an existing tape is cost-free. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem words_eq_flatMap (xs : List (List Bool)) :
    Subexp.MatrixProgramSupport.words xs = xs.flatMap Encoding.frame := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Subexp.MatrixProgramSupport.words, ih]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableHasDistance _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem no_local_rejection_iff {t D d : ℕ} (Q : Fin t → Fin D → SparseCode.F3) :
    (∀ x, ¬ wordRejects Q x d) ↔ SparseCode.HasDistance Q d := by
  constructor
  · intro h x hx hx0
    by_contra hlt
    exact h x ⟨hx, hx0, Nat.lt_of_not_ge hlt⟩
  · intro h x hx
    exact Nat.not_lt_of_ge (h x hx.1 hx.2.1) hx.2.2

theorem field_frames_eq {p d : ℕ} [Fact p.Prime] (x : Fin d → ZMod p) :
    (CodeCandidates.fieldWords x).flatMap Encoding.frame = scalarFrames (List.ofFn x) := by
  simp [CodeCandidates.fieldWords, scalarFrames, words_eq_flatMap,
    scalarWord_eq, List.map_ofFn, Function.comp_def]

theorem pair_frames_eq {p d : ℕ} [Fact p.Prime] (xs : List (Bool × Bool))
    (x : Fin d → ZMod p) (h : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x) :
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn x) := by
  rw [← field_frames_eq, ← h, List.flatMap_map]
  rfl

/-- Conversion is paid for afresh at every visit. The current counter remains
available, while the temporary input is consumed and all off-port stacks survive. -/
theorem copy_convert_eval {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S)
    (hci : current ≠ input) (hct : current ≠ scratch) (hti : scratch ≠ input)
    (hip : input ≠ payload) (xs : List (Bool × Bool)) (a : State 16 S)
    (hcurrent : a.stacks current = CodeCandidates.tupleBits xs)
    (hinput : a.stacks input = []) (hpayload : a.stacks payload = [])
    (hscratch : a.stacks scratch = []) :
    ∃ b, Eval (copyConvertCommand ternary current input payload scratch)
        (58 * xs.length + 16) a b ∧
      b.regs 4 = xs.any (CodeCandidates.invalidDigit ternary) ∧
      b.stacks input = [] ∧ b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ∧
      (∀ i, i ≠ input → i ≠ payload → b.stacks i = a.stacks i) := by
  let copied := SubexpSetupStorage.copyState current input a
  have hcopy := SubexpSetupStorage.copy_eval current input scratch a hci hct hti hscratch
  have hcopied : copied.stacks input = CodeCandidates.tupleBits xs := by
    simp [copied, SubexpSetupStorage.copyState_stack, hcurrent, hinput]
  let registers : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective _ _⟩
  let ports : Fin 2 ↪ Fin S := ⟨![input, payload], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨b, hrun, hflag, hempty, hword, hframe, _⟩ :=
    CodeCandidateProgram.convert_call ternary registers ports xs copied hcopied
  refine ⟨b, ?_, hflag, hempty, ?_, ?_⟩
  · have h := hcopy.seq hrun
    rw [hcurrent, CodeCandidates.tupleBits_length] at h
    convert h using 1
    · rfl
    · omega
  · have hcopypayload : copied.stacks payload = [] :=
      (SubexpSetupStorage.copyState_frame current input payload a (Ne.symm hip)).trans hpayload
    change b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ++ copied.stacks payload at hword
    simpa only [hcopypayload, List.append_nil] using hword
  · intro i hi hp
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · change input = i at hj
        exact hi hj.symm
      · change payload = i at hj
        exact hp hj.symm)]
    exact SubexpSetupStorage.copyState_frame current input i a hi

/-- Invalid digits pay for copying, conversion, the branch, and full payload
cleanup. They do not change any retained stack or the rejection latch. -/
theorem invalid_conversion_eval {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S) (accepted : Cmd 16 S)
    (hci : current ≠ input) (hct : current ≠ scratch) (hti : scratch ≠ input)
    (hip : input ≠ payload) (xs : List (Bool × Bool)) (a : State 16 S)
    (hcurrent : a.stacks current = CodeCandidates.tupleBits xs)
    (hinput : a.stacks input = []) (hpayload : a.stacks payload = [])
    (hscratch : a.stacks scratch = [])
    (hbad : xs.any (CodeCandidates.invalidDigit ternary) = true) :
    ∃ out, Eval (.seq (copyConvertCommand ternary current input payload scratch)
        (.ite 4 (SubexpSetupStorage.clearCmd payload) accepted))
        (68 * xs.length + 20) a out ∧ out.stacks = a.stacks := by
  obtain ⟨b, hconvert, hflag, hinput', hword, hframe⟩ :=
    copy_convert_eval ternary current input payload scratch hci hct hti hip xs a
      hcurrent hinput hpayload hscratch
  refine ⟨SubexpSetupStorage.clearState payload b, ?_, ?_⟩
  · have hclear := SubexpSetupStorage.clear_eval payload b
    rw [hword, List.length_reverse, CodeCandidates.scalarFrames_length] at hclear
    have h := hconvert.seq (Eval.ite_true (no := accepted) (hflag.trans hbad) hclear)
    convert h using 1; omega
  · funext i
    by_cases hp : i = payload
    · subst i
      simp [SubexpSetupStorage.clearState, hpayload]
    · by_cases hi : i = input
      · subst i
        simp [SubexpSetupStorage.clearState, hip, hinput', hinput]
      · simpa [SubexpSetupStorage.clearState, hp] using hframe i hi hp

theorem latchReject_eval (port : Fin 40) (a : ScanState) (b : Bool)
    (hport : a.stacks port = [b]) :
    ∃ out : ScanState, Eval (latchReject port) 3 a out ∧
      out.stacks port = [b || a.regs 15] ∧
      (∀ i, i ≠ port → out.stacks i = a.stacks i) := by
  let popped := (StructuredProgram.Atom.pop port 13 14).eval a
  let joined := (StructuredProgram.Atom.bor 13 13 15).eval popped
  let out := (StructuredProgram.Atom.push port 13).eval joined
  refine ⟨out, ?_, ?_, ?_⟩
  · exact (Eval.base (.atom _ a)).seq
      ((Eval.base (.atom _ popped)).seq (Eval.base (.atom _ joined)))
  · simp [out, joined, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,
      execInstr, readRegs, hport]
  · intro i hi
    simp [out, joined, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hi]

/-- A valid streamed local-code word is checked by the original bit arithmetic. Only
the one-bit rejection latch changes; this includes every off-port caller stack. -/
theorem local_stream_body_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x)
    (hvalid : xs.any (CodeCandidates.invalidDigit true) = false)
    (a : ScanState) (b : Bool)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hpayload : a.stacks 22 = []) (htmp : a.stacks 23 = [])
    (hcounter : a.stacks 24 = CodeCandidates.tupleBits xs)
    (hlatch : a.stacks 25 = [b]) (hcopy : a.stacks 27 = []) :
    ∃ steps out, steps ≤ callbackBudget t D d + 68 * D + 24 ∧
      Eval localStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 25 [b || decide (wordRejects Q x d)] := by
  have hlen : xs.length = D := by simpa using congrArg List.length hfields
  obtain ⟨c, hconvert, hflag, hcopy', hword, hcframe⟩ :=
    copy_convert_eval true 24 27 22 23 (by decide) (by decide) (by decide) (by decide)
      xs a hcounter hcopy hpayload htmp
  have hlow (i : Fin 22) : c.stacks ⟨i.val, by omega⟩ = a.stacks ⟨i.val, by omega⟩ := by
    apply hcframe <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp only at hv <;> omega
  have hwork : WorkEmpty (projectState id localStreamStacks c) := by
    intro i
    exact (hlow ⟨i.val, by omega⟩).trans (he i)
  have h35 : c.stacks 23 = [] := (hcframe 23 (by decide) (by decide)).trans htmp
  have h34 : c.stacks 22 = (scalarFrames (List.ofFn x)).reverse := by
    rw [hword, pair_frames_eq xs x hfields]
  obtain ⟨n, small, hn, hrun, hworkout, hreject, _, _, h34out, hframe⟩ :=
    wordCallback_eval Q x d
      (projectState id localStreamStacks c) hwork
      ((hlow 18).trans hm) ((hlow 19).trans ht) ((hlow 20).trans hd) h35 h34
  let middle := embedState id localStreamStacks c small
  have hcall := eval_call_from_state callbackProgram id localStreamStacks c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hrun 22 22)
  have hmid (i : Fin 24) : middle.stacks (localStreamStacks i) = small.stacks i :=
    embedState_stack id localStreamStacks c small (Fin.castAdd_injective _ _) i
  have hmidreg : middle.regs 15 = decide (wordRejects Q x d) :=
    (embedState_register id localStreamStacks c small Function.injective_id 15).trans hreject
  have hstacks : middle.stacks = a.stacks := by
    funext i
    by_cases hi : i.val < 18
    · let j : Fin 18 := ⟨i.val, hi⟩
      have hij : localStreamStacks (wordStacks j) = i := Fin.ext rfl
      rw [← hij, hmid, hworkout j]
      exact (he j).symm
    · by_cases h34i : i = 22
      · subst i
        exact (hmid 22).trans (h34out.trans hpayload.symm)
      · by_cases hi36 : i.val < 24
        · let j : Fin 24 := ⟨i.val, hi36⟩
          have hij : localStreamStacks j = i := Fin.ext rfl
          have hj34 : j ≠ 22 := by
            intro h
            apply h34i
            exact Fin.ext (by simpa [j] using congrArg Fin.val h)
          have h39i : i ≠ 27 := by
            intro h
            have hv := congrArg Fin.val h
            omega
          rw [← hij, hmid]
          exact (hframe j (by change 18 ≤ i.val; omega) hj34).trans (hcframe i h39i h34i)
        · have houter : middle.stacks i = c.stacks i := by
            apply embedState_stack_frame
            rintro ⟨j, hj⟩
            have hv := congrArg Fin.val hj
            change j.val = i.val at hv
            omega
          rw [houter]
          by_cases h39i : i = 27
          · subst i
            exact hcopy'.trans hcopy.symm
          · exact hcframe i h39i h34i
  obtain ⟨out, hor, hout, houtframe⟩ :=
    latchReject_eval 25 middle b ((congrFun hstacks 25).trans hlatch)
  refine ⟨(58 * xs.length + 16) + (n + 1 + 3 + 1), out, ?_, ?_, ?_⟩
  · rw [hlen]
    omega
  · exact hconvert.seq (Eval.ite_false (hflag.trans hvalid) (hcall.seq hor))
  · funext i
    by_cases hi : i = 25
    · subst i
      simpa [hmidreg] using hout
    · simpa [Function.update_of_ne hi] using (houtframe i hi).trans (congrFun hstacks i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem rejectedRank_field {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) [DecidablePred reject] (x : Fin d → ZMod p) :
    rejectedRank reject (CounterPrograms.value (CodeCandidates.fieldWords x).flatten) =
      decide (reject x) := by
  classical
  unfold rejectedRank
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hr⟩
    have heq : y = x := CodeCandidates.fieldWords_injective
      (ExecCNFTupleEnumeration.tuple_eq_of_shape_value (by simp) hy)
    simpa [heq] using hr
  · intro hx
    exact ⟨x, rfl, hx⟩

theorem tupleBits_eq (xs : List (Bool × Bool)) :
    CodeCandidates.tupleBits xs = Encoding.encodeList id (xs.map CodeCandidates.digitBits) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [CodeCandidates.tupleBits, Encoding.encodeList] at ih ⊢; exact ih

private theorem rejectedRank_invalid {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) (words : List (List Bool))
    (hshape : words.map List.length = List.replicate d (SubexpEnumerationPayload.scalarWidth p))
    (hinvalid : ∀ x : Fin d → ZMod p, words ≠ CodeCandidates.fieldWords x) :
    rejectedRank reject (CounterPrograms.value words.flatten) = false := by
  classical
  apply decide_eq_false (p := ∃ x : Fin d → ZMod p,
    CounterPrograms.value (CodeCandidates.fieldWords x).flatten = CounterPrograms.value words.flatten ∧
      reject x)
  rintro ⟨x, hx, _⟩
  exact hinvalid x (ExecCNFTupleEnumeration.tuple_eq_of_shape_value
    (hshape.trans (CodeCandidates.fieldWords_shape x).symm) hx.symm)

/-- Every width-two local-word candidate, including the invalid digits, has an
actual bounded callback execution. Only the persistent OR latch changes. -/
theorem local_stream_body {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (words : List (List Bool)) (hshape : words.map List.length = List.replicate D 2)
    (a : ScanState) (b : Bool)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hpayload : a.stacks 22 = []) (htmp : a.stacks 23 = [])
    (hcounter : a.stacks 24 = Encoding.encodeList id words)
    (hlatch : a.stacks 25 = [b]) (hcopy : a.stacks 27 = []) :
    ∃ steps out, steps ≤ callbackBudget t D d + 68 * D + 24 ∧
      Eval localStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 25
        [b || rejectedRank (fun x => wordRejects Q x d) (CounterPrograms.value words.flatten)] := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words D hshape
  have hc : a.stacks 24 = CodeCandidates.tupleBits xs := by
    rw [tupleBits_eq, hwords]
    exact hcounter
  subst D
  cases hv : xs.any (CodeCandidates.invalidDigit true) with
  | false =>
      obtain ⟨x, hx⟩ := CodeCandidates.ternary_digits_sound xs hv
      obtain ⟨steps, out, hn, hrun, hout⟩ := local_stream_body_valid Q x d xs hx hv
        a b he hm ht hd hpayload htmp hc hlatch hcopy
      refine ⟨steps, out, hn, hrun, ?_⟩
      rw [← hwords, hx, rejectedRank_field]
      exact hout
  | true =>
      have hrejected : rejectedRank (fun x => wordRejects Q x d)
          (CounterPrograms.value words.flatten) = false := by
        apply rejectedRank_invalid
        · have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
            norm_num [SubexpEnumerationPayload.scalarWidth]
          simpa only [hw] using hshape
        · intro x hx
          have hvalid := CodeCandidates.ternary_field_valid xs x (hwords.trans hx)
          rw [hv] at hvalid
          contradiction
      obtain ⟨out, hrun, hout⟩ := invalid_conversion_eval true 24 27 22 23
        (.seq (.call (ProgramLinking.liftProgram callbackProgram id localStreamStacks))
          (latchReject 25)) (by decide) (by decide) (by decide) (by decide)
        xs a hc hcopy hpayload htmp hv
      refine ⟨68 * xs.length + 20, out, by omega, hrun, ?_⟩
      rw [hrejected, Bool.or_false, hout, ← hlatch, Function.update_eq_self]

/-- The local-code iterator contract is discharged by the concrete byte-level
checker for every current tuple and every retained caller frame. -/
theorem local_rejection_body {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (base : ScanState)
    (he : WorkEmpty (projectState id localStreamStacks base))
    (hm : base.stacks 18 = matrixFrames Q) (ht : base.stacks 19 = List.replicate t true)
    (hd : base.stacks 20 = List.replicate d true)
    (hp : base.stacks 22 = []) (htmp : base.stacks 23 = []) (hcopy : base.stacks 27 = []) :
    RejectionBody localCounterPorts 25 localStreamBody D
      (callbackBudget t D d + 68 * D + 24) base (rejectedRank (fun x => wordRejects Q x d)) := by
  constructor
  intro words a hw ha hc _
  have hlo (i : Fin 24) : a.stacks (localStreamStacks i) = base.stacks (localStreamStacks i) := by
    apply ha.1
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [localStreamStacks, localCounterPorts] at hv
      omega
  obtain ⟨b, hb⟩ := ha.2
  obtain ⟨n, out, hn, hr, ho⟩ := local_stream_body Q d words hw a b
    (fun i => (hlo (wordStacks i)).trans (he i))
    ((hlo 18).trans hm) ((hlo 19).trans ht) ((hlo 20).trans hd)
    ((hlo 22).trans hp) ((hlo 23).trans htmp) hc hb
    ((ha.1 27 (by decide) (by decide) (by decide)).trans hcopy)
  exact ⟨n, out, hn, hr, by simpa [hb] using ho⟩

/-- Exhaustive rank rejection is equivalent to rejecting an actual field
word. This includes dimension zero and all invalid padded bit patterns. -/
theorem no_rejectedRank_iff {p d : ℕ} [Fact p.Prime]
    (hw : SubexpEnumerationPayload.scalarWidth p = 2)
    (reject : (Fin d → ZMod p) → Prop) [DecidablePred reject] :
    (List.range' 0 (4 ^ d)).any (rejectedRank reject) = false ↔ ∀ x, ¬ reject x := by
  classical
  constructor
  · intro h x hx
    have hp : 2 ^ (d * 2) = 4 ^ d := by
      rw [Nat.mul_comm d 2, pow_mul]
      norm_num
    have hlt := ExecCNFTupleOdometer.value_lt_power_length (CodeCandidates.fieldWords x).flatten
    rw [CodeCandidates.fieldWords_flatten_length, hw, hp] at hlt
    have hm : CounterPrograms.value (CodeCandidates.fieldWords x).flatten ∈
        List.range' 0 (4 ^ d) := by
      simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hlt
    have hn := List.any_eq_false.mp h _ hm
    rw [rejectedRank_field] at hn
    exact hn (decide_eq_true hx)
  · intro h
    apply List.any_eq_false.mpr
    intro rank _ htrue
    simp only [rejectedRank, decide_eq_true_eq] at htrue
    obtain ⟨x, _, hx⟩ := htrue
    exact h x hx

private theorem stream_body_budget (c dimension : ℕ) :
    c + 68 * dimension + 24 + 42 * dimension + 12 = c + 110 * dimension + 36 := by
  omega

/-- An actual local-code scan decides the full distance property, with time
and all-prefix source space on the same trace, for any supplied matrix. -/
theorem local_stream_runs {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : ScanState)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcopy : a.stacks 27 = [])
    (hcounter : a.stacks 24 = Encoding.encodeList id (List.replicate D [false, false]))
    (hscratch : a.stacks 26 = []) (hlatch : a.stacks 25 = [false])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ localStreamBudget t D d ∧
      Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) n
        (a.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
        (out.withPC none) ∧ RejectionFrame localCounterPorts 25 a out ∧ out.stacks 26 = [] ∧
      (out.stacks 25 = [false] ↔ SparseCode.HasDistance Q d) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max (B + callbackBudget t D d + 68 * D + 24) (40 * B + 7 * (6 * D + 1) + 4)) := by
  obtain ⟨n, out, hn, htrace, hf, hs, hl, hspace⟩ := rejection_scan_runs_space
    localCounterPorts 25 (by decide) (by decide) localStreamBody D
    (callbackBudget t D d + 68 * D + 24) (rejectedRank (fun x => wordRejects Q x d)) a false
    (local_rejection_body Q d a he hm ht hd hp htmp hcopy) hcounter hscratch hlatch B hB ha
  refine ⟨n, out, ?_, htrace, hf, hs, ?_, ?_⟩
  · simpa only [localStreamBudget, stream_body_budget] using hn
  · rw [hl]
    simp only [Bool.false_or, List.cons.injEq, and_true]
    rw [no_rejectedRank_iff (by norm_num [SubexpEnumerationPayload.scalarWidth])]
    exact no_local_rejection_iff Q
  · simpa only [Nat.add_assoc] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem zero_tuple_encoded_length (d : ℕ) :
    (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
  rw [Enumerators.encoded_shape_length (by simp :
    (List.replicate d [false, false]).map List.length = List.replicate d 2)]
  simp
  omega

private theorem scan_prepared_bound {S A : ℕ} (p : CodeCandidateProgram.ScanPorts S)
    (a prepared : State 16 S) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = CodeCandidateProgram.scanPreparedStacks p a) :
    ∀ i, (prepared.stacks i).length ≤ A + 6 * (a.stacks (p.stack 0)).length + 1 := by
  intro i
  rw [hp]
  unfold CodeCandidateProgram.scanPreparedStacks
  by_cases hi : i = p.stack 4
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    by_cases hj : i = p.stack 2
    · subst i
      rw [Function.update_self, zero_tuple_encoded_length]
      omega
    · rw [Function.update_of_ne hj]
      have hb := ha i
      omega

private theorem rejection_bool (bit : Bool) (P : Prop) [Decidable P]
    (h : bit = false ↔ P) : bit = !(decide P) := by
  cases bit <;> simp_all

/-- Complete actual local-matrix checker: it initializes its word counter,
checks every word, computes the Boolean acceptance bit, then clears temporary
state. Time and the uniform source-prefix space bound describe the same run. -/
theorem local_checker_runs_oai {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (hD : a.stacks 21 = List.replicate D true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
    (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = []) :
    ∃ steps out, Eval localChecker steps a out ∧
      steps ≤ localStreamBudget t D d + 15 * D + 2 * coreSpace A D (callbackBudget t D d) + 18 ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧ out.stacks = a.stacks ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled localChecker 21 25) prefixSteps
          (a.withPC (some (compiled localChecker 21 25).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          40 * A + 15 * D + 43 * coreSpace A D (callbackBudget t D d) + 18) := by
  classical
  have hcore : ∀ prepared : ScanState,
      prepared.stacks = CodeCandidateProgram.scanPreparedStacks localScanPorts a →
      ∃ (n : ℕ) (middle : ScanState), n ≤ localStreamBudget t D d ∧
        Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) n
          (prepared.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
          (middle.withPC none) ∧
        middle.stacks 25 = [!(decide (SparseCode.HasDistance Q d))] ∧
        (∀ i, i ≠ 24 → i ≠ 25 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) prefixSteps
            (prepared.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ coreSpace A D (callbackBudget t D d) := by
    intro prepared hprepared
    have hf (i : Fin 40) (hi : i ≠ 24) (hj : i ≠ 25) : prepared.stacks i = a.stacks i := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts, hi, hj]
    have hb : ∀ i, (prepared.stacks i).length ≤ A + 6 * D + 1 := by
      simpa [localScanPorts, hD] using scan_prepared_bound localScanPorts a prepared ha hprepared
    have hcounter' : prepared.stacks 24 = Encoding.encodeList id (List.replicate D [false, false]) := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts, hD]
    have hlatch' : prepared.stacks 25 = [false] := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts]
    have he' : WorkEmpty (projectState id localStreamStacks prepared) := by
      intro i
      apply (hf _ ?_ ?_).trans (he i)
      all_goals
        intro h
        have hv := congrArg Fin.val h
        change i.val = _ at hv
        have hi := i.isLt
        omega
    obtain ⟨n, middle, hn, htrace, hframe, hscratch', hdecide, hspace⟩ :=
      local_stream_runs Q d prepared he' ((hf 18 (by decide) (by decide)).trans hm)
        ((hf 19 (by decide) (by decide)).trans ht) ((hf 20 (by decide) (by decide)).trans hd)
        ((hf 22 (by decide) (by decide)).trans hp) ((hf 23 (by decide) (by decide)).trans htmp)
        ((hf 27 (by decide) (by decide)).trans hcopy) hcounter'
        ((hf 26 (by decide) (by decide)).trans hscratch) hlatch'
        (A + 6 * D + 1) (by omega) hb
    obtain ⟨bit, hbit⟩ := hframe.latch_word
    have hbitvalue : bit = !(decide (SparseCode.HasDistance Q d)) :=
      rejection_bool bit _ (by simpa [hbit] using hdecide)
    refine ⟨n, middle, hn, htrace, hbit.trans (congrArg List.singleton hbitvalue), ?_, hspace⟩
    intro i hi hj
    by_cases hs : i = 26
    · subst i
      exact hscratch'.trans ((hf 26 (by decide) (by decide)).trans hscratch).symm
    · exact hframe.frame i hi hs hj
  obtain ⟨steps, out, hrun, htime, hanswer, hout, hspace⟩ :=
    CodeCandidateProgram.scanWrapper_resources localScanPorts
      (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody)
      a (!(decide (SparseCode.HasDistance Q d))) hcopy hcounter htmp hlatch ha hcore
  refine ⟨steps, out, hrun, ?_, ?_, hout, ?_⟩
  · simpa [localScanPorts, hD] using htime
  · simp only [hanswer, Bool.not_not, decide_eq_true_eq]
  · have hsum (A d b : ℕ) : 40 * A + 15 * d + 40 * b + 3 * b + 18 =
        40 * A + 15 * d + 43 * b + 18 := by omega
    simpa [localChecker, localScanPorts, hD, hsum] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs_oai
