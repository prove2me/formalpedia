-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:35:00.257246+00:00
-- url     : https://prove2.me/submissions/bfbb4856-7630-4bf5-9722-f3a1f709c747

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem literalCode_lt {n : ℕ} (l : SAT.Literal (Fin n)) : literalCode l < 2 * n := by
  have hv := l.variable.isLt
  cases hp : l.positive <;> simp [literalCode, hp] ; omega

theorem mem_clauseNumbers_lt {n : ℕ} {C : SAT.Clause (Fin n)} {a : ℕ}
    (h : a ∈ clauseNumbers C) : a < 2 * n := by
  have hi : a ∈ C.image literalCode := by simpa [clauseNumbers] using h
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
  exact literalCode_lt l

theorem length_encodeClause_upper {n : ℕ} (C : SAT.Clause (Fin n)) :
    (encodeList encodeNat (clauseNumbers C)).length ≤ 1 + (4 * n + 4) * C.card := by
  have h := length_encodeList_upper encodeNat (clauseNumbers C) (2 * n + 1)
    (fun a ha => by rw [length_encodeNat]; have := mem_clauseNumbers_lt ha; omega)
  have hc : 2 * (2 * n + 1) + 2 = 4 * n + 4 := by omega
  simpa only [length_clauseNumbers, hc] using h

/-- A polynomial upper bound for the actual encoding, without any semantic oracle. -/
theorem formulaBitLength_upper {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    formulaBitLength F ≤ n + 2 + (4 + (8 * n + 8) * k) * F.card := by
  have hp : ∀ as ∈ cnfNumbers F,
      (encodeList encodeNat as).length ≤ 1 + (4 * n + 4) * k := by
    intro as has
    have hi : as ∈ F.image clauseNumbers := by simpa [cnfNumbers] using has
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hi
    exact (length_encodeClause_upper C).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hw C hC)) _)
  have h := length_encodeList_upper (encodeList encodeNat) (cnfNumbers F)
    (1 + (4 * n + 4) * k) hp
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change (encodeCNFBody F).length ≤ _ at h
  calc
    n + 1 + (encodeCNFBody F).length
        ≤ n + 1 + (1 + (2 * (1 + (4 * n + 4) * k) + 2) * F.card) :=
          Nat.add_le_add_left h _
    _ = n + 2 + (4 + (8 * n + 8) * k) * F.card := by ring

end SubexponentialSAT.Encoding

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CopySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix storage of the actual preserving copy table. Empty destination
and temporary stacks permit the original per-stack envelope to be reused. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

open BitProgram

private theorem copyWeight_step {r s : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (hstep : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  cases hpc : a.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      simp only [step, hpc, Option.map, Option.some.injEq] at hstep
      rw [← hstep]
      fin_cases pc
      · cases hx : a.stacks src <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hsd.symm, hst.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hst, htd.symm]
        omega
      · cases hx : a.stacks tmp <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hst, htd.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hsd.symm, hst.symm]
        omega
      · simp [copyWeight, execInstr, hpc, hsd, htd]
      · simp [copyWeight, execInstr, hpc]

private theorem copyWeight_trace {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  induction ht with
  | refl => exact le_rfl
  | cons hs _ ih => exact ih.trans (copyWeight_step src dst tmp value present hsd hst htd hs)

theorem copyProgram_frame {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b)
    (i : Fin s) (his : i ≠ src) (hid : i ≠ dst) (hit : i ≠ tmp) :
    b.stacks i = a.stacks i := by
  have hsingle {a b : Cfg r s 8}
      (hs : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
      b.stacks i = a.stacks i := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some pc =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        fin_cases pc <;> simp [execInstr, his, hid, hit]
  induction ht with
  | refl => rfl
  | cons hs _ ih => exact ih.trans (hsingle hs)

private theorem ports_le_copyWeight {r s : ℕ} (src dst tmp : Fin s) (present : Fin r)
    (a : Cfg r s 8) :
    (a.stacks src).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks dst).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks tmp).length ≤ copyWeight src dst tmp present a := by
  unfold copyWeight
  cases a.pc with
  | none => dsimp; omega
  | some pc => dsimp; split_ifs <;> omega

/-- Exact local copying never exceeds the source's original word length;
every off-port caller word retains its own independent bound. -/
theorem copyProgram_stack_bound {r s steps frameBound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (hframe : ∀ i, i ≠ src → i ≠ dst → i ≠ tmp → (a.stacks i).length ≤ frameBound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ max (a.stacks src).length frameBound := by
  have hweight : copyWeight src dst tmp present b ≤ (a.stacks src).length := by
    have h := copyWeight_trace src dst tmp value present hsd hst htd ht
    simpa [copyWeight, hentry, hdst, htmp] using h
  obtain ⟨hsrc, hdst', htmp'⟩ := ports_le_copyWeight src dst tmp present b
  intro i
  by_cases hi : i = src
  · subst i
    exact (hsrc.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hd : i = dst
  · subst i
    exact (hdst'.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hw : i = tmp
  · subst i
    exact (htmp'.trans hweight).trans (Nat.le_max_left _ _)
  rw [copyProgram_frame src dst tmp value present ht i hi hd hw]
  exact (hframe i hi hd hw).trans (Nat.le_max_right _ _)

theorem copyProgram_no_growth {r s steps bound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ bound := by
  intro i
  exact (copyProgram_stack_bound src dst tmp value present hsd hst htd hentry hdst htmp
    (fun j _ _ _ => ha j) ht i).trans (max_le (ha src) le_rfl)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CNFNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Raw input normalization for the frozen counting manuscript, lines 1758–1762.
The ambient type remains `Fin n` throughout, including unused variables.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

variable {n : ℕ}

theorem formulaSet_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact D.toFinset_card_le.trans (h D hD)

private theorem encodeList_length_perm {α : Type*} (enc : α → List Bool)
    {as bs : List α} (h : as.Perm bs) :
    (Encoding.encodeList enc as).length = (Encoding.encodeList enc bs).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b as => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem encodeList_length_map_congr {α β γ : Type*}
    (enc₁ : β → List Bool) (enc₂ : γ → List Bool) (f : α → β) (g : α → γ)
    (as : List α) (h : ∀ a ∈ as, (enc₁ (f a)).length = (enc₂ (g a)).length) :
    (Encoding.encodeList enc₁ (as.map f)).length =
      (Encoding.encodeList enc₂ (as.map g)).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, Encoding.length_encodeList_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Sorting literals and clauses changes their order but not the serialized size.
The hypotheses exclude both literal repetitions and semantically duplicate clauses. -/
theorem encodeRawCNFBody_length_eq (F : RawCNF n)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup) :
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (F.map (List.map Encoding.literalCode))).length =
      (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length := by
  have hclause (C : List (SAT.Literal (Fin n))) (h : C ∈ F) :
      (C.map Encoding.literalCode).Perm (Encoding.clauseNumbers (ExecCNF.clauseSet C)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((hC C h).map Encoding.literalCode_injective) (Finset.sort_nodup _ _)
    ext i
    simp [ExecCNF.clauseSet]
  have hformula : ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers).Perm
      (Encoding.cnfNumbers (ExecCNF.formulaSet F)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      (hF.map Encoding.clauseNumbers_injective) (Finset.sort_nodup _ _)
    ext C
    simp [ExecCNF.formulaSet]
  calc
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (F.map (List.map Encoding.literalCode))).length =
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers)).length := by
      rw [List.map_map]
      apply encodeList_length_map_congr
      intro C h
      exact encodeList_length_perm Encoding.encodeNat (hclause C h)
    _ = (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length :=
      encodeList_length_perm _ hformula

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

/-- A coarse polynomial clause bound, sufficient for the search cost. -/
theorem clause_card_le (F : CNF (Fin n)) (k : ℕ)
    (hF : ∀ C ∈ F, C.card ≤ k) : F.card ≤ (k + 1) * (2 * n + 1) ^ k := by
  let enc := fun C : Clause (Fin n) => C.image Encoding.literalCode
  have hinj : Function.Injective enc := Finset.image_injective Encoding.literalCode_injective
  have hsub : F.image enc ⊆ (Finset.range (k + 1)).biUnion
      (fun j => (Finset.range (2 * n)).powersetCard j) := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    refine Finset.mem_biUnion.mpr ⟨D.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hF D hD)), ?_⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Encoding.literalCode_lt l)
    · exact Finset.card_image_of_injective _ Encoding.literalCode_injective
  calc
    F.card = (F.image enc).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (k + 1)).biUnion
        (fun j => (Finset.range (2 * n)).powersetCard j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (k + 1)).card * (2 * n + 1) ^ k := by
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      simp only [Finset.card_powersetCard, Finset.card_range]
      calc
        (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
        _ ≤ (2 * n + 1) ^ j := Nat.pow_le_pow_left (by omega) _
        _ ≤ (2 * n + 1) ^ k := Nat.pow_le_pow_right (by omega)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (k + 1) * (2 * n + 1) ^ k := by rw [Finset.card_range]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem formulaBitLength_le (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    Encoding.formulaBitLength F ≤ formulaBound n k :=
  (Encoding.formulaBitLength_upper F hF).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (SparsePriority.clause_card_le F k hF)) _)

theorem encodeBody_length_le (F : RawCNF n) (k : ℕ)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup)
    (hwidth : WidthAtMost k (ExecCNF.formulaSet F)) :
    (encodeBody F).length ≤ formulaBound n k := by
  have h := formulaBitLength_le (ExecCNF.formulaSet F) k hwidth
  rw [Encoding.formulaBitLength_eq] at h
  rw [encodeBody, encodeRawCNFBody_length_eq F hC hF]
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSBoundarySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical storage at the depth-first controller boundary.

Only framed formula bodies occur on the pending stack. The mathematical depth
is a proof index and is not serialized. Both children, the current formula,
the declared-variable word, and the two count words are charged simultaneously.
These bounds apply to the actual fixed frontier and accumulator routines after
injective port relocation. The final DFS must still establish its boundary
invariant and bounds for the concrete selector, splitter, and leaf commands.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

open BitProgram StructuredCalls

/-- Actual cleanup never increases any stack, at any prefix. No bound on
elapsed time is needed: its finite table contains only pop, branch and halt. -/
theorem clearProgram_stack_length_le {r s steps : ℕ}
    (src : Fin s) (value present : Fin r) {a b : Cfg r s 3}
    (htrace : Trace (StackRoutines.clearProgram src value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
  have hstep {a b : Cfg r s 3}
      (hs : step (StackRoutines.clearProgram src value present) a = some b) :
      ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some label =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        intro i
        fin_cases label
        · by_cases hi : i = src
          · subst i
            simp [execInstr]
          · simp [execInstr, hi]
        · simp [execInstr]
        · simp [execInstr]
  induction htrace with
  | refl => exact fun _ => le_rfl
  | cons hs ht ih => exact fun i => (ih i).trans (hstep hs i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual finite count-word positivity suffix. The counting body is integrated
separately; this suffix never interprets the least significant bit as SAT. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem leafPorts_eq : leafPorts = (List.finRange 896).map ABI.leafStacks :=
  leafPortsWrapped.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem copyWord_eval (src dst scratch : Fin 1220) (a : State 80 1220)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hblank : a.stacks scratch = []) :
    Eval (copyWord src dst scratch) (7 * (a.stacks src).length + 5) a
      (copiedWord src dst a) :=
  Eval.call _ (ListRegisterProgram.copy_run src dst scratch 72 73 hsd hst htd
    (by decide) a.regs a.stacks hblank)

theorem clearSequence_eval (ports : List (Fin 1220)) (a : State 80 1220) (B : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ (2 * B + 3) * ports.length ∧
      Eval (clearSequence ports) steps a b ∧
      (∀ i ∈ ports, b.stacks i = []) ∧
      (∀ i, i ∉ ports → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  induction ports generalizing a with
  | nil => exact ⟨0, a, by simp, .base (.skip a), by simp, by simp, hbound⟩
  | cons port rest ih =>
    have hlocal : ∀ i, ((clearOutputState port a).stacks i).length ≤ B := by
      intro i
      by_cases hi : i = port
      · subst i; simp [clearOutputState]
      · simpa [clearOutputState, hi] using hbound i
    obtain ⟨steps, b, hs, he, hc, hf, hb⟩ := ih (clearOutputState port a) hlocal
    refine ⟨2 * (a.stacks port).length + 3 + steps, b, ?_,
      (clearOutput_eval port a).seq he, ?_, ?_, hb⟩
    · have := hbound port
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with hip | hi
      · subst i
        by_cases hp : port ∈ rest
        · exact hc port hp
        · rw [hf port hp]; simp [clearOutputState]
      · exact hc i hi
    · intro i hi
      have hip : i ≠ port := fun h => hi (List.mem_cons.mpr (.inl h))
      have hir : i ∉ rest := fun h => hi (List.mem_cons.mpr (.inr h))
      rw [hf i hir]
      simp [clearOutputState, hip]

theorem clearLeaf_eval (a : State 80 1220) (B : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 896 * (2 * B + 3) ∧ Eval clearLeaf steps a b ∧
      (∀ j : Fin 896, b.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨steps, b, hs, he, hc, hf, hb⟩ := clearSequence_eval leafPorts a B hbound
  refine ⟨steps, b, ?_, he, ?_, ?_, hb⟩
  · simpa [leafPorts_eq, Nat.mul_comm] using hs
  · intro j; exact hc _ (by simp [leafPorts_eq])
  · intro i hi
    exact hf i (by simpa [leafPorts_eq] using hi)

theorem copyWord_bound (src dst : Fin 1220) (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hd : a.stacks dst = []) :
    ∀ i, ((copiedWord src dst a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = dst
  · subst i; simpa [copiedWord, StackRoutines.copyStacks, hd] using ha src
  · simpa [copiedWord, StackRoutines.copyStacks, hi] using ha i

theorem clearOutput_bound (port : Fin 1220) (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((clearOutputState port a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = port
  · subst i; simp [clearOutputState]
  · simpa [clearOutputState, hi] using ha i

theorem resetRegisters_eval (ports : List (Fin 80)) (a : State 80 1220) :
    Eval (resetRegisters ports) ports.length a (resetRegisterState ports a) := by
  induction ports generalizing a with
  | nil => simpa [resetRegisters, resetRegisterState] using (Eval.base (.skip a))
  | cons i rest ih =>
    have h := (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    convert h using 1
    · rfl
    · simp only [List.length_cons, Nat.add_comm]
    · apply CounterForPrograms.data_ext
      · funext j
        by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
          simp [resetRegisterState, StructuredProgram.Atom.eval,
            StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
            execInstr, hj, hr]
      · rfl

theorem resetLeafRegisters_eval (a : State 80 1220) :
    Eval resetLeafRegisters 40 a (resetLeafState a) := by
  simpa [resetLeafRegisters, resetLeafState, leafRegisterPorts] using
    resetRegisters_eval leafRegisterPorts a

theorem loadLeaf_eval (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1815 * B + 2746 ∧ Eval loadLeaf steps a b ∧
      b.stacks 1104 = a.stacks 265 ∧ b.stacks 1105 = a.stacks 267 ∧
      b.stacks 1106 = a.stacks 264 ∧ b.stacks 1219 = [] ∧
      (∀ j : Fin 896, ABI.leafStacks j ≠ 1104 → ABI.leafStacks j ≠ 1105 →
        ABI.leafStacks j ≠ 1106 → b.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧ (∀ j, b.regs (ABI.leafRegisters j) = false) := by
  obtain ⟨t, e, ht, he, hempty, hframe, hb⟩ := clearLeaf_eval a B ha
  let d0 := clearOutputState 1219 (resetLeafState e)
  let d1 := copiedWord 265 1104 d0
  let d2 := copiedWord 267 1105 d1
  let d3 := copiedWord 264 1106 d2
  have hfr (i : Fin 1220) (hi : i.val < 320) : e.stacks i = a.stacks i := by
    apply hframe
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 320 + j.val = i.val at hv
    omega
  have h1104 : e.stacks 1104 = [] := hempty 784
  have h1105 : e.stacks 1105 = [] := hempty 785
  have h1106 : e.stacks 1106 = [] := hempty 786
  have hreset := resetLeafRegisters_eval e
  have h0 := clearOutput_eval 1219 (resetLeafState e)
  have h1 := copyWord_eval 265 1104 1219 d0 (by decide) (by decide) (by decide)
    (by simp [d0, clearOutputState])
  have h2 := copyWord_eval 267 1105 1219 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks])
  have h3 := copyWord_eval 264 1106 1219 d2 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks])
  have hb0 := clearOutput_bound 1219 (resetLeafState e) B hb
  have hb1 := copyWord_bound 265 1104 d0 B hb0 (by simp [d0, clearOutputState, resetLeafState, resetRegisterState, h1104])
  have hb2 := copyWord_bound 267 1105 d1 B hb1
    (by simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks, resetLeafState, resetRegisterState, h1105])
  have hb3 := copyWord_bound 264 1106 d2 B hb2
    (by simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks, resetLeafState, resetRegisterState, h1106])
  refine ⟨t + (40 + (2 * (e.stacks 1219).length + 3 +
    (7 * (d0.stacks 265).length + 5 + (7 * (d1.stacks 267).length + 5 +
      (7 * (d2.stacks 264).length + 5))))), d3, ?_,
      he.seq (hreset.seq (h0.seq (h1.seq (h2.seq h3)))),
      ?_, ?_, ?_, ?_, ?_, ?_, hb3, ?_⟩
  · have := hb 1219
    have h265 : (d0.stacks 265).length ≤ B := hb0 265
    have h267 : (d1.stacks 267).length ≤ B := hb1 267
    have h264 : (d2.stacks 264).length ≤ B := hb2 264
    omega
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1104, hfr 265 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1105, hfr 267 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1106, hfr 264 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks]
  · intro j h4 h5 h6
    have hj : ABI.leafStacks j ≠ 1219 := by
      intro h; have hv := congrArg Fin.val h
      change 320 + j.val = 1219 at hv
      omega
    simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h4, h5, h6, hj, hempty j]
  · intro i hi hs
    have h4 : i ≠ 1104 := by intro h; subst i; exact hi ⟨784, rfl⟩
    have h5 : i ≠ 1105 := by intro h; subst i; exact hi ⟨785, rfl⟩
    have h6 : i ≠ 1106 := by intro h; subst i; exact hi ⟨786, rfl⟩
    simpa [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h4, h5, h6, hs] using hframe i hi
  · intro j
    have h72 : ABI.leafRegisters j ≠ 72 := by
      intro h; have hv := congrArg Fin.val h
      change 32 + j.val = 72 at hv
      omega
    have h73 : ABI.leafRegisters j ≠ 73 := by
      intro h; have hv := congrArg Fin.val h
      change 32 + j.val = 73 at hv
      omega
    simp [d3, d2, d1, d0, copiedWord, clearOutputState, readRegs,
      resetLeafState, resetRegisterState, leafRegisterPorts, h72, h73]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPrimeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

private theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => rfl
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have haa : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          exact congrArg Nat.succ (ih ht' hb hc)

/-- The exact instruction count of a terminating structured execution is
unique as well as its result. This allows proved execution bounds to be used
for every actual occurrence of a subroutine in a larger trace. -/
theorem eval_steps_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : n = m := by
  have h := terminal_trace_steps_unique
    (StructuredCalls.compiled_halt_trace h₁ input output)
    (StructuredCalls.compiled_halt_trace h₂ input output) rfl rfl
  omega

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeaf
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual adapters for the streamed counting leaf. Both initial code rows
and newly generated rows use the canonical modulus word's exact width. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- Clearing a port never enlarges any retained word, including before return. -/
theorem clearOutput_space (port : Fin 1220) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (clearOutput port) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearOutput port) 256 256) prefixSteps
        (a.withPC (some (compiled (clearOutput port) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 72 73)
        (compiled (clearOutput port) 256 256) (siteAddress (clearOutput port))
        (exitAddress (clearOutput port)) (compiled_site (clearOutput port) 256 256) ht
      intro prefixSteps c _ hc i
      exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
        port 72 73 hc i).trans (ha i)

/-- The fixed bank cleanup preserves the incoming per-stack bound. -/
theorem clearSequence_space (ports : List (Fin 1220)) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (clearSequence ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearSequence ports) 256 256) prefixSteps
        (a.withPC (some (compiled (clearSequence ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clearOutput_space port first ha
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 256 256)
          exact StructuredSpace.sequence_stack_bound first second 256 256 hfirst
            (ih second hmiddle) (compiled (clearSequence (port :: rest)) 256 256)
            (siteAddress (clearSequence (port :: rest)))
            (exitAddress (clearSequence (port :: rest)))
            (compiled_site (clearSequence (port :: rest)) 256 256)

theorem resetRegisters_space (ports : List (Fin 80)) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (resetRegisters ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (resetRegisters ports) 256 256) prefixSteps
        (a.withPC (some (compiled (resetRegisters ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst : ∀ prefixSteps c, prefixSteps ≤ 1 →
              Trace (compiled (.base (.atom (.set port false))) 256 256) prefixSteps
                (a.withPC (some (compiled (.base (.atom (.set port false))) 256 256).entry)) c →
              ∀ i, (c.stacks i).length ≤ bound := by
            intro prefixSteps c hp hc
            have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
            rcases hcases with rfl | rfl
            · cases hc
              exact ha
            · rw [trace_same_length_unique hc
                (compiled_trace (Eval.base (.atom (.set port false) a)) 256 256)]
              exact ha
          cases first with
          | base h =>
              cases h with
              | atom =>
                  exact StructuredSpace.sequence_stack_bound
                    (Eval.base (.atom (.set port false) a)) second 256 256 hfirst
                    (ih second ha) (compiled (resetRegisters (port :: rest)) 256 256)
                    (siteAddress (resetRegisters (port :: rest)))
                    (exitAddress (resetRegisters (port :: rest)))
                    (compiled_site (resetRegisters (port :: rest)) 256 256)

/-- The copy table preserves its source and never needs a word longer than
that source when its destination and scratch are initially empty. -/
theorem copyWord_space (src dst scratch : Fin 1220) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (copyWord src dst scratch) steps a b)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hdst : a.stacks dst = []) (htmp : a.stacks scratch = [])
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (copyWord src dst scratch) 256 256) prefixSteps
        (a.withPC (some (compiled (copyWord src dst scratch) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.copyProgram src dst scratch 72 73)
        (compiled (copyWord src dst scratch) 256 256) (siteAddress (copyWord src dst scratch))
        (exitAddress (copyWord src dst scratch))
        (compiled_site (copyWord src dst scratch) 256 256) ht
      intro prefixSteps c _ hc
      exact CopySpace.copyProgram_no_growth src dst scratch 72 73 hsd hst htd
        rfl hdst htmp ha hc

/-- Clearing, resetting and copying the three actual leaf inputs retain the
same per-stack envelope, even when the ambient numeric words are padded. -/
theorem loadLeaf_space {steps B : ℕ} {a b : State 80 1220}
    (heval : Eval loadLeaf steps a b) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled loadLeaf 256 256) prefixSteps
        (a.withPC (some (compiled loadLeaf 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  obtain ⟨t, e, _, he, hempty, _, hb⟩ := clearLeaf_eval a B ha
  let d0 := clearOutputState 1219 (resetLeafState e)
  let d1 := copiedWord 265 1104 d0
  let d2 := copiedWord 267 1105 d1
  have h1104 : e.stacks 1104 = [] := hempty 784
  have h1105 : e.stacks 1105 = [] := hempty 785
  have h1106 : e.stacks 1106 = [] := hempty 786
  have hclear : DisjointReuse.DFSVisit.BoundedEval clearLeaf t a e B :=
    ⟨he, clearSequence_space leafPorts he ha⟩
  have hreset : DisjointReuse.DFSVisit.BoundedEval resetLeafRegisters 40 e (resetLeafState e) B :=
    ⟨resetLeafRegisters_eval e,
      resetRegisters_space leafRegisterPorts (resetLeafRegisters_eval e) hb⟩
  have h0e := clearOutput_eval 1219 (resetLeafState e)
  have h0 : DisjointReuse.DFSVisit.BoundedEval (clearOutput 1219)
      (2 * ((resetLeafState e).stacks 1219).length + 3) (resetLeafState e) d0 B :=
    ⟨h0e, clearOutput_space 1219 h0e hb⟩
  have htmp0 : d0.stacks 1219 = [] := by simp [d0, clearOutputState]
  have hdst1 : d0.stacks 1104 = [] := by
    simp [d0, clearOutputState, resetLeafState, resetRegisterState, h1104]
  have h1e := copyWord_eval 265 1104 1219 d0 (by decide) (by decide) (by decide) htmp0
  have h1 : DisjointReuse.DFSVisit.BoundedEval (copyWord 265 1104 1219)
      (7 * (d0.stacks 265).length + 5) d0 d1 B :=
    ⟨h1e, copyWord_space 265 1104 1219 h1e (by decide) (by decide) (by decide)
      hdst1 htmp0 h0.final_bound⟩
  have htmp1 : d1.stacks 1219 = [] := by
    simp [d1, copiedWord, StackRoutines.copyStacks, htmp0]
  have hdst2 : d1.stacks 1105 = [] := by
    simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1105]
  have h2e := copyWord_eval 267 1105 1219 d1 (by decide) (by decide) (by decide) htmp1
  have h2 : DisjointReuse.DFSVisit.BoundedEval (copyWord 267 1105 1219)
      (7 * (d1.stacks 267).length + 5) d1 d2 B :=
    ⟨h2e, copyWord_space 267 1105 1219 h2e (by decide) (by decide) (by decide)
      hdst2 htmp1 h1.final_bound⟩
  have htmp2 : d2.stacks 1219 = [] := by
    simp [d2, copiedWord, StackRoutines.copyStacks, htmp1]
  have hdst3 : d2.stacks 1106 = [] := by
    simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1106]
  have h3e := copyWord_eval 264 1106 1219 d2 (by decide) (by decide) (by decide) htmp2
  have h3 : DisjointReuse.DFSVisit.BoundedEval (copyWord 264 1106 1219)
      (7 * (d2.stacks 264).length + 5) d2 (copiedWord 264 1106 d2) B :=
    ⟨h3e, copyWord_space 264 1106 1219 h3e (by decide) (by decide) (by decide)
      hdst3 htmp2 h2.final_bound⟩
  have whole := hclear.seq (hreset.seq (h0.seq (h1.seq (h2.seq h3))))
  have ht := SubexpPrimeProgram.eval_steps_unique whole.eval heval 256 256
  simpa only [loadLeaf, ht] using whole.space

/-- The loaded leaf is small independently of the suspended DFS envelope.
The two parameter word caps come from concrete pre-DFS production. -/
theorem loadLeaf_input_bound_oai {n k parameterBound B : ℕ} (threshold : List Bool)
    (F : DisjointReuse.RawCNF n) (a : State 80 1220)
    (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
    (hr : DisjointReuse.DFSVisit.LeafReady k threshold parameterBound F a)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1815 * B + 2746 ∧
      DisjointReuse.DFSVisit.BoundedEval loadLeaf steps a b B ∧
      b.stacks 1104 = DisjointReuse.SparseCountProgram.encodeBody F ∧
      BinaryArithmetic.toNat (b.stacks 1105) = n ∧
      BinaryArithmetic.toNat (b.stacks 1106) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
      (∀ j : Fin 896, (b.stacks (ABI.leafStacks j)).length ≤
        DisjointReuse.SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) ∧
      (∀ j : Fin 896, j ≠ 784 → j ≠ 785 → j ≠ 786 →
        b.stacks (ABI.leafStacks j) = []) ∧
      (∀ j, b.regs (ABI.leafRegisters j) = false) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i) := by
  obtain ⟨steps, b, ht, he, hformula, hn, hB, _, hempty, hframe, _, hregs⟩ :=
    loadLeaf_eval a B ha
  have hbody := DisjointReuse.SparseCountProgram.encodeBody_length_le F k hv.literal_nodup
    hv.clause_nodup (DisjointReuse.formulaSet_width_le F hv.width)
  have empty (j : Fin 896) (h4 : j ≠ 784) (h5 : j ≠ 785) (h6 : j ≠ 786) :
      b.stacks (ABI.leafStacks j) = [] := by
    apply hempty j
    · exact fun h => h4 (ABI.leafStacks.injective h)
    · exact fun h => h5 (ABI.leafStacks.injective h)
    · exact fun h => h6 (ABI.leafStacks.injective h)
  refine ⟨steps, b, ht, ⟨he, loadLeaf_space he ha⟩,
    hformula.trans hr.current, ?_, ?_, ?_, empty, hregs, hframe⟩
  · rw [hn]; exact hr.ambient
  · rw [hB]; exact hr.dimension
  · intro j
    by_cases h4 : j = 784
    · subst j
      change (b.stacks 1104).length ≤ _
      rw [hformula, hr.current]
      omega
    by_cases h5 : j = 785
    · subst j
      change (b.stacks 1105).length ≤ _
      rw [hn]
      have h := hr.dimension_length
      omega
    by_cases h6 : j = 786
    · subst j
      change (b.stacks 1106).length ≤ _
      rw [hB]
      have h := hr.occurrence_length
      omega
    rw [empty j h4 h5 h6]
    exact Nat.zero_le _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound_oai
