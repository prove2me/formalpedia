-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:02:01.933877+00:00
-- url     : https://prove2.me/submissions/20395bb4-de48-4f4e-9416-6655ffe1d64f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_local_checker_runs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SparseCodeSearch_core_runs

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

theorem matrixWords_of_vector {p rows cols : ℕ} [Fact p.Prime]
    (v : Fin (rows * cols) → ZMod p) :
    matrixWords (fun i j => v (finProdFinEquiv (i, j))) = fieldWords v := by
  unfold matrixWords
  congr 1
  funext i
  exact congrArg v (finProdFinEquiv.apply_symm_apply i)

/-- Every range-checked current matrix is an actual ternary matrix, with
the supplied row-major convention and including zero-sized dimensions. -/
theorem ternary_matrix_digits_sound (xs : List (Bool × Bool)) (rows cols : ℕ)
    (hlen : xs.length = rows * cols) (hvalid : xs.any (invalidDigit true) = false) :
    ∃ matrix : Fin rows → Fin cols → ZMod 3, xs.map digitBits = matrixWords matrix := by
  obtain ⟨v, hv⟩ := ternary_digits_sound xs hvalid
  let flat : Fin (rows * cols) → ZMod 3 := fun i => v (Fin.cast hlen.symm i)
  refine ⟨fun i j => flat (finProdFinEquiv (i,j)), ?_⟩
  rw [matrixWords_of_vector, hv]
  exact List.ofFn_congr hlen (fun i => scalarBits (v i))

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

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

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

theorem conditional_false_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = false) (heval : StructuredCalls.Eval no steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled no inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled no inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q)))

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

/-- Runtime preparation retains one bounded-width tuple, including the
one-bit terminator when the matrix has zero entries. All other stacks survive. -/
theorem prepareSearch_eval {S : ℕ} (ports : Fin 4 ↪ Fin S)
    (a : StructuredCalls.State 16 S)
    (hi : a.stacks (ports 1) = []) (hc : a.stacks (ports 2) = [])
    (hs : a.stacks (ports 3) = []) :
    ∃ b, StructuredCalls.Eval (prepareSearch ports)
        (15 * (a.stacks (ports 0)).length + 11) a b ∧
      b.stacks = Function.update a.stacks (ports 2)
        (Encoding.encodeList id (List.replicate (a.stacks (ports 0)).length [false, false])) := by
  let copied : StructuredCalls.State 16 S :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (ports 0) (ports 1) a.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram (ports 0) (ports 1) (ports 3) 0 1))
      (7 * (a.stacks (ports 0)).length + 5) a copied :=
    .call _ (ListRegisterProgram.copy_run _ _ _ _ _
      (ports.injective.ne (by decide)) (ports.injective.ne (by decide))
      (ports.injective.ne (by decide)) (by decide) a.regs a.stacks hs)
  have hcopied : copied.stacks (ports 1) = a.stacks (ports 0) := by
    simp [copied, StackRoutines.copyStacks, hi]
  have hcopiedFrame (i : Fin S) (hne : i ≠ ports 1) : copied.stacks i = a.stacks i := by
    simp [copied, StackRoutines.copyStacks, hne]
  have houtput : copied.stacks ((searchInitializePorts ports) 1) = [] := by
    change copied.stacks (ports 2) = []
    exact (hcopiedFrame _ (ports.injective.ne (by decide))).trans hc
  obtain ⟨b, hinit, hempty, htuple, hframe, _⟩ :=
    initialize_call scanRegisters (searchInitializePorts ports) copied houtput
  refine ⟨b, ?_, ?_⟩
  · have h := hcopy.seq hinit
    change StructuredCalls.Eval (prepareSearch ports)
      ((7 * (a.stacks (ports 0)).length + 5) +
        (8 * (copied.stacks (ports 1)).length + 6)) a b at h
    rw [hcopied] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · have hcounter : b.stacks (ports 2) = Encoding.encodeList id
        (List.replicate (a.stacks (ports 0)).length [false, false]) := by
      change b.stacks (ports 2) = Encoding.encodeList id
        (List.replicate (copied.stacks (ports 1)).length [false, false]) at htuple
      simpa only [hcopied] using htuple
    have hinput : b.stacks (ports 1) = [] := hempty
    funext i
    by_cases h2 : i = ports 2
    · subst i
      simpa using hcounter
    by_cases h1 : i = ports 1
    · subst i
      simp [h2, hinput, hi]
    · rw [Function.update_of_ne h2, hframe i (by
        rintro ⟨j, hj⟩
        fin_cases j
        · exact h1 hj.symm
        · exact h2 hj.symm)]
      exact hcopiedFrame i h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

theorem matrixWords_eq_words_flatten (rows : List (List (List Bool))) :
    matrixWords rows = words rows.flatten := by
  induction rows with
  | nil => rfl
  | cons ys rows ih => simp [matrixWords, List.flatten_cons, words_append, ih]

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
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

theorem framedVector_eq_scalarFrames {p d : ℕ} [Fact p.Prime]
    (v : Fin d → ZMod p) : framedVector v = scalarFrames (List.ofFn v) := by
  simp [framedVector, SubexpTupleRefinement.encodeTuple,
    StackEncoding.encodeDataStack_eq_flatMap, framedScalarCode,
    Subexp.BasisTransposeProgram.framedCode, scalarFrames,
    words_eq_flatMap, SubexpEnumerationPayload.scalarCode]
  rw [← List.map_ofFn]
  simp only [List.flatMap_map, scalarWord_eq]

theorem flattenMatrix_ofFn {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) :
    List.ofFn (flattenMatrix M) =
      (List.ofFn fun i => List.ofFn fun j => M i j).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hidx : (finProdFinEquiv (i,j)).val = i.val * cols + j.val := by
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  change flattenMatrix M ⟨i.val * cols + j.val, _⟩ = M i j
  rw [show (⟨i.val * cols + j.val, _⟩ : Fin (rows * cols)) =
      finProdFinEquiv (i,j) from Fin.ext hidx.symm]
  simp [flattenMatrix]

theorem framedMatrix_eq_matrixFrames {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : framedMatrix M = matrixFrames M := by
  rw [framedMatrix, framedVector_eq_scalarFrames, flattenMatrix_ofFn]
  simp [scalarFrames, matrixFrames, words_eq_flatMap,
    Subexp.MatrixVectorProgram.matrixWords_eq_words_flatten,
    List.map_flatten, List.map_ofFn, Function.comp_def]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

/-- Matrix scalar order agrees with the original row-major matrix encoding.
The converter therefore stages one actual matrix without recoding a family. -/
theorem pair_matrix_frames_eq {p rows cols : ℕ} [Fact p.Prime]
    (xs : List (Bool × Bool)) (M : Fin rows → Fin cols → ZMod p)
    (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords M) :
    CodeCandidates.scalarFrames xs = matrixFrames M := by
  calc
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn (flattenMatrix M)) :=
      pair_frames_eq xs (flattenMatrix M) h
    _ = framedMatrix M := (framedVector_eq_scalarFrames (flattenMatrix M)).symm
    _ = matrixFrames M := framedMatrix_eq_matrixFrames M

theorem installMatrix_eval {S : ℕ} (payload matrix : Fin S) (hpm : payload ≠ matrix)
    (word : List Bool) (a : State 16 S) (hp : a.stacks payload = word.reverse) :
    ∃ out, Eval (installMatrix payload matrix)
        (2 * (a.stacks matrix).length + 3 * word.length + 6) a out ∧
      out.stacks payload = [] ∧ out.stacks matrix = word ∧
      (∀ i, i ≠ payload → i ≠ matrix → out.stacks i = a.stacks i) := by
  let cleared := SubexpSetupStorage.clearState matrix a
  let out := SubexpScanPrimitives.afterTransfer cleared payload matrix 0 1
  have hc := SubexpSetupStorage.clear_eval matrix a
  have ht := SubexpScanPrimitives.transfer_eval cleared payload matrix 0 1 hpm (by decide)
  have hpayload : cleared.stacks payload = word.reverse := by
    simpa [cleared, SubexpSetupStorage.clearState, hpm] using hp
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · have he := hc.seq ht
    rw [hpayload, List.length_reverse] at he
    convert he using 1
    · rfl
    · omega
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm]
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm,
      cleared, SubexpSetupStorage.clearState, hp]
  · intro i hi hj
    simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      cleared, SubexpSetupStorage.clearState, hi, hj]

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

theorem tupleBits_eq (xs : List (Bool × Bool)) :
    CodeCandidates.tupleBits xs = Encoding.encodeList id (xs.map CodeCandidates.digitBits) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [CodeCandidates.tupleBits, Encoding.encodeList] at ih ⊢; exact ih

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- A complete checker call keeps its local every-prefix space proof after
embedding; the eight persistent outer-search stacks are counted separately. -/
theorem lift_checker_resources (checker : Cmd 16 40) (input output : Fin 40)
    (a : MatrixState) (small : ScanState) {n A B : ℕ}
    (hrun : Eval checker n (projectState id checkerPorts a) small)
    (hrestore : small.stacks = (projectState id checkerPorts a).stacks)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ n → Trace (compiled checker input output) k
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) c →
      ∀ i, (c.stacks i).length ≤ B) :
    ∃ out, Eval (liftChecker checker input output) (n + 1) a out ∧
      out.stacks = a.stacks ∧ out.regs = small.regs ∧
      (∀ k c, k ≤ n + 1 → Trace (compiled (liftChecker checker input output) 40 42) k
        (a.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max B A) := by
  let out := embedState id checkerPorts a small
  have ht := compiled_halt_trace hrun input output
  have hs := StructuredSpace.compiled_halt_stack_bound hrun input output hspace
  have hc := eval_call_from_state (compiled checker input output) id checkerPorts a
    Function.injective_id (Fin.castAdd_injective _ _) ht
  have hinitial : ProgramLinking.embedCfg id checkerPorts id none
      (a.withPC (none : Option (Fin (size checker + 1))))
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) =
      a.withPC (some (compiled checker input output).entry) := by
    change (embedState id checkerPorts a (projectState id checkerPorts a)).withPC _ = _
    rw [embedState_project id checkerPorts a Function.injective_id (Fin.castAdd_injective _ _)]
    rfl
  have hlift := ProgramLinking.liftProgram_trace (compiled checker input output) id checkerPorts
    (a.withPC none) Function.injective_id (Fin.castAdd_injective _ _) ht
  rw [hinitial] at hlift
  have hlift' : Trace (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (n + 1) (a.withPC (some (compiled checker input output).entry)) (out.withPC none) := by
    simpa [out, embedState, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC] using hlift
  have hliftspace := StructuredSpace.liftProgram_stack_bound
    (compiled checker input output) id checkerPorts (a.withPC none)
    Function.injective_id (Fin.castAdd_injective _ _) ht hs ha
  rw [hinitial] at hliftspace
  refine ⟨out, hc, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, checkerPorts j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack id checkerPorts a small (Fin.castAdd_injective _ _) j).trans
        (congrFun hrestore j)
    · exact embedState_stack_frame id checkerPorts a small i hi
  · funext i
    exact embedState_register id checkerPorts a small Function.injective_id i
  · exact StructuredSpace.call_stack_bound
      (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (compiled (liftChecker checker input output) 40 42)
      (siteAddress (liftChecker checker input output)) (exitAddress (liftChecker checker input output))
      (compiled_site (liftChecker checker input output) 40 42) hlift' hliftspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- Invalid matrix digits are rejected by actual finite control and all of
conversion's retained buffers are cleared. -/
theorem matrix_candidate_invalid (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40)
    (xs : List (Bool × Bool)) (a : MatrixState) (A : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (hscratch : a.stacks 45 = [])
    (hbad : xs.any (CodeCandidates.invalidDigit ternary) = true) :
    ∃ out, Eval (matrixCandidate ternary matrix checker input output)
        (68 * xs.length + 21) a out ∧
      out.regs 15 = false ∧ out.stacks = a.stacks ∧
      (∀ k c, k ≤ 68 * xs.length + 21 →
        Trace (compiled (matrixCandidate ternary matrix checker input output) 40 42) k
          (a.withPC (some (compiled (matrixCandidate ternary matrix checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ A + 68 * xs.length + 21) := by
  obtain ⟨b, hc, hf, _, hw, hframe⟩ := copy_convert_eval ternary 40 43 44 45
    (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch
  let cleared := SubexpSetupStorage.clearState 44 b
  let out := (StructuredProgram.Atom.set (s := 48) 15 false).eval cleared
  have hclear := SubexpSetupStorage.clear_eval 44 b
  rw [hw, List.length_reverse, CodeCandidates.scalarFrames_length] at hclear
  have hr : Eval (matrixCandidate ternary matrix checker input output)
      (68 * xs.length + 21) a out := by
    have h := hc.seq (Eval.ite_true (no := .seq (installMatrix 44 matrix)
      (liftChecker checker input output)) (hf.trans hbad)
      (hclear.seq (Eval.base (.atom (.set 15 false) cleared))))
    convert h using 1
    · rfl
    · omega
  refine ⟨out, hr, by simp [out, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    execInstr, StructuredProgram.State.ofCfg], ?_, ?_⟩
  · obtain ⟨out', hr', hout'⟩ := invalid_conversion_eval ternary 40 43 44 45
      (.seq (installMatrix 44 matrix) (liftChecker checker input output))
      (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch hbad
    have hclearstacks : cleared.stacks = a.stacks := by
      have h := hc.seq (Eval.ite_true (no := .seq (installMatrix 44 matrix)
        (liftChecker checker input output)) (hf.trans hbad) hclear)
      have heq := Eval.final_unique 40 h hr'
      exact congrArg StructuredProgram.State.stacks heq |>.trans hout'
    simpa [out, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC] using hclearstacks
  · intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    omega

/-- This composition lemma charges conversion and replacement locally, while
using the separately proved complete checker's space bound for its long scan.
The next two theorems instantiate this interface with the actual checkers. -/
theorem matrix_candidate_valid (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40)
    (hm43 : matrix ≠ 43) (hm44 : matrix ≠ 44)
    (xs : List (Bool × Bool)) (word : List Bool) (hword : CodeCandidates.scalarFrames xs = word)
    (a : MatrixState) (A T B : ℕ) (P : Prop)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (hscratch : a.stacks 45 = [])
    (hvalid : xs.any (CodeCandidates.invalidDigit ternary) = false)
    (hchecker : ∀ prepared : MatrixState, prepared.stacks = Function.update a.stacks matrix word →
      ∃ n out, n ≤ T ∧ Eval (liftChecker checker input output) n prepared out ∧
        (out.regs 15 = true ↔ P) ∧ out.stacks = prepared.stacks ∧
        ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
          (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ B) :
    ∃ n out, n ≤ T + 2 * A + 73 * xs.length + 23 ∧
      Eval (matrixCandidate ternary matrix checker input output) n a out ∧
      (out.regs 15 = true ↔ P) ∧ out.stacks = Function.update a.stacks matrix word ∧
      (∀ k c, k ≤ n → Trace (compiled (matrixCandidate ternary matrix checker input output) 40 42) k
        (a.withPC (some (compiled (matrixCandidate ternary matrix checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * xs.length + 23) B) := by
  obtain ⟨b, hcopy, hflag, hb43, hb44, hbframe⟩ := copy_convert_eval ternary 40 43 44 45
    (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch
  have hbm : b.stacks matrix = a.stacks matrix := hbframe matrix hm43 hm44
  have hwlen : word.length = 5 * xs.length := by
    rw [← hword, CodeCandidates.scalarFrames_length]
  obtain ⟨prepared, hinstall, hp44, hpm, hpframe⟩ := installMatrix_eval 44 matrix (Ne.symm hm44)
    word b (by rw [hb44, hword])
  have hprepared : prepared.stacks = Function.update a.stacks matrix word := by
    funext i
    by_cases hi : i = matrix
    · subst i
      simpa using hpm
    · rw [Function.update_of_ne hi]
      by_cases h44 : i = 44
      · subst i
        exact hp44.trans hpayload.symm
      · rw [hpframe i h44 hi]
        by_cases h43 : i = 43
        · subst i
          exact hb43.trans hinput.symm
        · exact hbframe i h43 h44
  obtain ⟨n, out, hn, hcheck, haccept, hrestore, hcheckspace⟩ := hchecker prepared hprepared
  let bound := max (3 * A + 73 * xs.length + 23) B
  have hcopyspace : ∀ k c, k ≤ 58 * xs.length + 16 →
      Trace (compiled (copyConvertCommand ternary 40 43 44 45) 40 42) k
        (a.withPC (some (compiled (copyConvertCommand ternary 40 43 44 45) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hinstallspace : ∀ k c, k ≤ 2 * (b.stacks matrix).length + 3 * word.length + 6 →
      Trace (compiled (installMatrix 44 matrix) 40 42) k
        (b.withPC (some (compiled (installMatrix 44 matrix) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    have hb := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le (compiled_trace hcopy 40 42) i
    change (c.stacks i).length ≤ (b.stacks i).length + k at hg
    change (b.stacks i).length ≤ (a.stacks i).length + (58 * xs.length + 16) at hb
    have hi := ha i
    have hm := ha matrix
    rw [hbm, hwlen] at hk
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hcheckspace' : ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
      (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    exact (hcheckspace k c hk ht i).trans (Nat.le_max_right _ _)
  have hsequence := StructuredSpace.sequence_stack_bound hinstall hcheck 40 42 hinstallspace hcheckspace'
    (compiled (.seq (installMatrix 44 matrix) (liftChecker checker input output)) 40 42)
    (siteAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (exitAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (compiled_site _ 40 42)
  let rejected : Cmd 16 48 := .seq (SubexpSetupStorage.clearCmd 44) (.base (.atom (.set 15 false)))
  let tail : Cmd 16 48 := .ite 4 rejected (.seq (installMatrix 44 matrix) (liftChecker checker input output))
  have htail : Eval tail ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1) b out :=
    .ite_false (hflag.trans hvalid) (hinstall.seq hcheck)
  have htailspace := StructuredSpace.conditional_false_stack_bound (hflag.trans hvalid)
    (hinstall.seq hcheck) 40 42 hsequence (compiled tail 40 42) (siteAddress tail)
    (exitAddress tail) (compiled_site tail 40 42)
  refine ⟨(58 * xs.length + 16) + ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1), out,
    ?_, hcopy.seq htail, haccept, hrestore.trans hprepared, ?_⟩
  · have hm := ha matrix
    rw [hbm, hwlen]
    omega
  · exact StructuredSpace.sequence_stack_bound hcopy htail 40 42 hcopyspace htailspace
      (compiled (matrixCandidate ternary matrix checker input output) 40 42)
      (siteAddress (matrixCandidate ternary matrix checker input output))
      (exitAddress (matrixCandidate ternary matrix checker input output))
      (compiled_site (matrixCandidate ternary matrix checker input output) 40 42)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem updated_matrix_bound (a prepared : MatrixState) (A : ℕ) (matrix : Fin 48)
    (word : List Bool) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = Function.update a.stacks matrix word) :
    ∀ i, (prepared.stacks i).length ≤ A + word.length := by
  intro i
  rw [hp]
  by_cases hi : i = matrix
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (Nat.le_add_right _ _)

theorem local_matrix_candidate_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords Q)
    (hvalid : xs.any (CodeCandidates.invalidDigit true) = false)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : ∀ i : Fin 18, a.stacks (Fin.castAdd 30 i) = [])
    (ht : a.stacks 19 = List.replicate t true) (hd : a.stacks 20 = List.replicate d true)
    (hD : a.stacks 21 = List.replicate D true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
    (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = [])
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
    ∃ n out, n ≤ matrixCheckTime A (t * D) D (callbackBudget t D d) (localStreamBudget t D d) +
        2 * A + 73 * (t * D) + 23 ∧
      Eval localMatrixCandidate n a out ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧
      out.stacks = Function.update a.stacks 18 (matrixFrames Q) ∧
      (∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
        (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (t * D) + 23)
          (matrixCheckSpace A (t * D) D (callbackBudget t D d))) := by
  have hlen : xs.length = t * D := by simpa [CodeCandidates.matrixWords] using congrArg List.length hfields
  have hword := pair_matrix_frames_eq xs Q hfields
  have hwordlen : (matrixFrames Q).length = 5 * (t * D) := by
    rw [← hword, CodeCandidates.scalarFrames_length, hlen]
  have result := matrix_candidate_valid true 18 localChecker 21 25
      (by decide) (by decide) xs (matrixFrames Q) hword a A
      (matrixCheckTime A (t * D) D (callbackBudget t D d) (localStreamBudget t D d))
      (matrixCheckSpace A (t * D) D (callbackBudget t D d)) (SparseCode.HasDistance Q d)
      ha hcurrent hinput hpayload houtertmp hvalid
  rw [hlen] at result
  apply result
  intro prepared hprepared
  have hf (i : Fin 48) (hi : i ≠ 18) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hb : ∀ i, (prepared.stacks i).length ≤ A + 5 * (t * D) := by
    simpa [hwordlen] using updated_matrix_bound a prepared A 18 (matrixFrames Q) ha hprepared
  have he' : WorkEmpty (projectState id localStreamStacks (projectState id checkerPorts prepared)) := by
    intro i
    apply (hf (Fin.castAdd 30 i) ?_).trans (he i)
    intro h
    have hv := congrArg Fin.val h
    change i.val = 18 at hv
    omega
  have hm : (projectState id checkerPorts prepared).stacks 18 = matrixFrames Q := by
    change prepared.stacks 18 = _
    rw [hprepared, Function.update_self]
  obtain ⟨n, small, hrun, hn, haccept, hrestore, hspace⟩ := local_checker_runs Q d
    (projectState id checkerPorts prepared) (A + 5 * (t * D)) (fun i => hb (checkerPorts i)) he' hm
    ((hf 19 (by decide)).trans ht) ((hf 20 (by decide)).trans hd) ((hf 21 (by decide)).trans hD)
    ((hf 22 (by decide)).trans hp) ((hf 23 (by decide)).trans htmp)
    ((hf 24 (by decide)).trans hcounter) ((hf 25 (by decide)).trans hlatch)
    ((hf 26 (by decide)).trans hscratch) ((hf 27 (by decide)).trans hcopy)
  obtain ⟨out, hcall, hout, hregs, hbound⟩ := lift_checker_resources localChecker 21 25
    prepared small hrun hrestore hb hspace
  refine ⟨n + 1, out, ?_, hcall, ?_, hout, hbound⟩
  · unfold matrixCheckTime
    omega
  · simpa only [hregs] using haccept

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem LocalMatrixReady.of_frame {t D d : ℕ} {a b : MatrixState}
    (ha : LocalMatrixReady t D d a) (hf : ∀ i, i ≠ 18 → b.stacks i = a.stacks i) :
    LocalMatrixReady t D d b := by
  refine ⟨?_, (hf 19 (by decide)).trans ha.rows, (hf 20 (by decide)).trans ha.distance,
    (hf 21 (by decide)).trans ha.dimension, (hf 22 (by decide)).trans ha.payload,
    (hf 23 (by decide)).trans ha.scratch, (hf 24 (by decide)).trans ha.counter,
    (hf 25 (by decide)).trans ha.latch, (hf 26 (by decide)).trans ha.counterScratch,
    (hf 27 (by decide)).trans ha.copy, (hf 43 (by decide)).trans ha.outerInput,
    (hf 44 (by decide)).trans ha.outerPayload, (hf 45 (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf _ ?_).trans (ha.work i)
  intro h
  have hv := congrArg Fin.val h
  change i.val = 18 at hv
  omega

theorem LocalMatrixReady.frame {t D d : ℕ} {a b : MatrixState}
    (ha : LocalMatrixReady t D d a) (hf : ∀ i, i ≠ 18 → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) :
    LocalMatrixReady t D d b := by
  refine ⟨?_, (hf 19 (by decide) (by decide) (by decide) (by decide)).trans ha.rows, (hf 20 (by decide) (by decide) (by decide) (by decide)).trans ha.distance,
    (hf 21 (by decide) (by decide) (by decide) (by decide)).trans ha.dimension, (hf 22 (by decide) (by decide) (by decide) (by decide)).trans ha.payload,
    (hf 23 (by decide) (by decide) (by decide) (by decide)).trans ha.scratch, (hf 24 (by decide) (by decide) (by decide) (by decide)).trans ha.counter,
    (hf 25 (by decide) (by decide) (by decide) (by decide)).trans ha.latch, (hf 26 (by decide) (by decide) (by decide) (by decide)).trans ha.counterScratch,
    (hf 27 (by decide) (by decide) (by decide) (by decide)).trans ha.copy, (hf 43 (by decide) (by decide) (by decide) (by decide)).trans ha.outerInput,
    (hf 44 (by decide) (by decide) (by decide) (by decide)).trans ha.outerPayload, (hf 45 (by decide) (by decide) (by decide) (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf (Fin.castAdd 30 i) ?_ ?_ ?_ ?_).trans (ha.work i)
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 18 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 40 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 41 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 42 at hv
    omega

/-- Every current outer-counter tuple is processed by the actual local matrix
command, including invalid scalar digits and losing code candidates. -/
theorem local_matrix_candidate_runs (t D d : ℕ) (a : MatrixState) (A : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ A) (hcap : 5 * (t * D) ≤ A)
    (hready : LocalMatrixReady t D d a) (words : List (List Bool))
    (hshape : words.map List.length = List.replicate (t * D) 2)
    (hcurrent : a.stacks 40 = Encoding.encodeList id words) :
    ∃ n out, n ≤ candidateBudget A (t * D) D (callbackBudget t D d) (localStreamBudget t D d) ∧
      Eval localMatrixCandidate n a out ∧ LocalMatrixReady t D d out ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ A) ∧
      (out.regs 15 = true → ∃ Q : Fin t → Fin D → SparseCode.F3,
        out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d) ∧
      (∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
        (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ candidateSpace A (t * D) D (callbackBudget t D d)) := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words (t * D) hshape
  have hc : a.stacks 40 = CodeCandidates.tupleBits xs := by rw [hcurrent, tupleBits_eq, hwords]
  cases hvalid : xs.any (CodeCandidates.invalidDigit true) with
  | false =>
    obtain ⟨Q, hQ⟩ := CodeCandidates.ternary_matrix_digits_sound xs t D hlen hvalid
    obtain ⟨n, out, hn, hr, haccept, hout, hspace⟩ := local_matrix_candidate_valid Q d xs hQ hvalid a A
      ha hready.work hready.rows hready.distance hready.dimension hready.payload hready.scratch
      hready.counter hready.latch hready.counterScratch hready.copy hc
      hready.outerInput hready.outerPayload hready.outerScratch
    have hf : ∀ i, i ≠ 18 → out.stacks i = a.stacks i := by
      intro i hi
      rw [hout, Function.update_of_ne hi]
    refine ⟨n, out, hn, hr, hready.of_frame hf, hf, ?_, ?_, hspace⟩
    · intro i
      by_cases hi : i = 18
      · subst i
        rw [hout, Function.update_self, ← pair_matrix_frames_eq xs Q hQ,
          CodeCandidates.scalarFrames_length, hlen]
        exact hcap
      · rw [hf i hi]
        exact ha i
    · intro hy
      refine ⟨Q, ?_, haccept.mp hy⟩
      rw [hout, Function.update_self]
  | true =>
    obtain ⟨out, hr, hfalse, hout, hspace⟩ := matrix_candidate_invalid true 18 localChecker 21 25
      xs a A ha hc hready.outerInput hready.outerPayload hready.outerScratch hvalid
    have hf : ∀ i, i ≠ 18 → out.stacks i = a.stacks i := fun i _ => congrFun hout i
    refine ⟨68 * xs.length + 21, out, ?_, hr, hready.of_frame hf, hf, ?_, ?_, ?_⟩
    · unfold candidateBudget
      rw [hlen]
      omega
    · simpa only [hout] using ha
    · simp [hfalse]
    · intro k c hk ht i
      have hb := hspace k c hk ht i
      rw [hlen] at hb
      exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * (t * D) + 23).trans
        (Nat.le_max_left _ _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram


private theorem invariant_full_bound (matrix : Fin 48) (Ready : State 16 48 → Prop)
    (Good : List Bool → Prop) (base a : State 16 48) (d B : ℕ)
    (hcap : 6 * d + 1 ≤ B) (ha : Invariant matrix Ready Good base B a)
    (words : List (List Bool)) (hw : words.map List.length = List.replicate d 2)
    (hc : a.stacks 40 = Encoding.encodeList id words) (hs : a.stacks 41 = []) :
    ∀ i, (a.stacks i).length ≤ B := by
  intro i
  by_cases h40 : i = 40
  · subst i
    rw [hc, Enumerators.encoded_shape_length hw]
    simp only [List.sum_replicate, smul_eq_mul, List.length_replicate]
    omega
  by_cases h41 : i = 41
  · subst i
    simp [hs]
  · exact ha.bound i h40 h41


private theorem cleanup_eval (a : State 16 48) :
    ∃ out, Eval cleanup (2 * (a.stacks 40).length + 2 * (a.stacks 42).length + 6) a out ∧
      out.stacks = Function.update (Function.update a.stacks 40 []) 42 [] := by
  let b : State 16 48 := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 40 a.stacks⟩
  let out : State 16 48 := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 42 b.stacks⟩
  have h1 : Eval (.call (StackRoutines.clearProgram (s := 48) 40 (0 : Fin 16) 1))
      (2 * (a.stacks 40).length + 3) a b := .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  have h2 : Eval (.call (StackRoutines.clearProgram (s := 48) 42 (0 : Fin 16) 1))
      (2 * (b.stacks 42).length + 3) b out := .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  have hb : b.stacks 42 = a.stacks 42 := by simp [b, StackRoutines.clearStacks]
  refine ⟨out, ?_, rfl⟩
  have h := h1.seq h2
  rw [hb] at h
  convert h using 1
  · rfl
  · omega

/-- Setup, exhaustive first-success search, readout retention and cleanup form
one actual run. All candidate services in this intermediate lemma are explicit
fixed commands, instantiated below by the native local and graph checkers. -/
theorem command_runs (candidate : Cmd 16 48) (matrix : Fin 48)
    (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (hcopy : ∀ a, Ready a → a.stacks 45 = [])
    (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
    (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate d 2 → Ready a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
        (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks matrix)) ∧
        ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (a.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ C)
    (target : List (List Bool)) (htarget : target.map List.length = List.replicate d 2)
    (haccept : ∀ a, Ready a → (∀ i, (a.stacks i).length ≤ B) →
      a.stacks 40 = Encoding.encodeList id target →
      ∃ n b, Eval candidate n a b ∧ b.regs 15 = true)
    (a : State 16 48) (ha : Ready a) (hab : ∀ i, (a.stacks i).length ≤ B)
    (hdim : (a.stacks 46).length = d)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = [])
    (h43 : a.stacks 43 = []) :
    ∃ n out, n ≤ timeBudget d B T C ∧ Eval (command candidate) n a out ∧
      Good (out.stacks matrix) ∧ Ready out ∧
      (∀ i, i ≠ matrix → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      ∀ k c, k ≤ n → Trace (compiled (command candidate) 46 matrix) k
        (a.withPC (some (compiled (command candidate) 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
  obtain ⟨prepared, hp, hpstacks⟩ := prepareSearch_eval setupPorts a h43 h40 (hcopy a ha)
  have hptime : 15 * (a.stacks (setupPorts 0)).length + 11 = 15 * d + 11 := by
    simp [setupPorts, hdim]
  rw [hptime] at hp
  have hprepared : prepared.stacks = Function.update a.stacks 40
      (Encoding.encodeList id (List.replicate d [false, false])) := by
    rw [show setupPorts 2 = 40 by decide, show setupPorts 0 = 46 by decide,
      hdim] at hpstacks
    exact hpstacks
  have hf (i : Fin 48) (hi : i ≠ 40) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hI : Invariant matrix Ready Good a B prepared := by
    refine ⟨hready a prepared ha (fun i _ hi _ _ => hf i hi), ?_, ?_, ?_⟩
    · intro i hi _
      rw [hf i hi]
      exact hab i
    · intro hn
      exact (hn ((hf 42 (by decide)).trans h42)).elim
    · intro i _ hi _ _
      exact hf i hi
  have hc : prepared.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) := by
    rw [hprepared, Function.update_self]
  have hs : prepared.stacks 41 = [] := (hf 41 (by decide)).trans h41
  obtain ⟨nc, middle, hnc, hcore, hmiddle, hms, hmc, _, hgood, hcoreSpace⟩ :=
    core_runs candidate matrix hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap
      hchecks target htarget haccept a prepared hI hc hs
  have hmiddleBound := invariant_full_bound matrix Ready Good a middle d B hcap hmiddle
    (List.replicate d [false, false]) (by simp) hmc hms
  obtain ⟨out, hclean, hout⟩ := cleanup_eval middle
  have houtFrame (i : Fin 48) (hi40 : i ≠ 40) (hi42 : i ≠ 42) :
      out.stacks i = middle.stacks i := by
    rw [hout, Function.update_of_ne hi42, Function.update_of_ne hi40]
  have houtBound : ∀ i, (out.stacks i).length ≤ B := by
    intro i
    by_cases hi40 : i = 40
    · subst i
      simp [hout]
    by_cases hi42 : i = 42
    · subst i
      simp [hout]
    · rw [houtFrame i hi40 hi42]
      exact hmiddleBound i
  have hcall : Eval (.call (core candidate)) nc prepared middle := .call _ hcore
  have hprepSpace : ∀ k c, k ≤ 15 * d + 11 →
      Trace (compiled (prepareSearch setupPorts) 46 matrix) k
        (a.withPC (some (compiled (prepareSearch setupPorts) 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := hab i
    unfold spaceBudget
    omega
  have hcallSpace : ∀ k c, k ≤ nc → Trace (compiled (.call (core candidate)) 46 matrix) k
      (prepared.withPC (some (compiled (.call (core candidate)) 46 matrix).entry)) c →
      ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    have h := StructuredSpace.call_stack_bound (core candidate)
      (compiled (.call (core candidate)) 46 matrix) (siteAddress (.call (core candidate)))
      (exitAddress (.call (core candidate)))
      (fun pc => compiled_site (.call (core candidate)) 46 matrix pc) hcore hcoreSpace
    intro k c hk ht i
    have hb := h k c hk ht i
    unfold spaceBudget
    omega
  have hcleanSpace : ∀ k c, k ≤ 2 * (middle.stacks 40).length + 2 * (middle.stacks 42).length + 6 →
      Trace (compiled cleanup 46 matrix) k
        (middle.withPC (some (compiled cleanup 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (middle.stacks i).length + k at hg
    have hi := hmiddleBound i
    have h40b := hmiddleBound 40
    have h42b := hmiddleBound 42
    unfold spaceBudget
    omega
  refine ⟨(15 * d + 11) + (nc + (2 * (middle.stacks 40).length +
    2 * (middle.stacks 42).length + 6)), out, ?_, hp.seq (hcall.seq hclean), ?_, ?_, ?_, houtBound, ?_⟩
  · have h40b := hmiddleBound 40
    have h42b := hmiddleBound 42
    unfold timeBudget
    omega
  · rwa [houtFrame matrix hm40 hm42]
  · exact hready middle out hmiddle.ready (fun i _ hi40 _ hi42 => houtFrame i hi40 hi42)
  · intro i him
    by_cases hi40 : i = 40
    · subst i
      simp [hout, h40]
    by_cases hi42 : i = 42
    · subst i
      simp [hout, h42]
    rw [houtFrame i hi40 hi42]
    by_cases hi41 : i = 41
    · subst i
      exact hms.trans h41.symm
    · exact hmiddle.frame i him hi40 hi41 hi42
  · have htail := StructuredSpace.sequence_stack_bound hcall hclean 46 matrix
      hcallSpace hcleanSpace (compiled (.seq (.call (core candidate)) cleanup) 46 matrix)
      (siteAddress (.seq (.call (core candidate)) cleanup))
      (exitAddress (.seq (.call (core candidate)) cleanup)) (compiled_site _ 46 matrix)
    exact StructuredSpace.sequence_stack_bound hp (hcall.seq hclean) 46 matrix hprepSpace htail
      (compiled (command candidate) 46 matrix) (siteAddress (command candidate))
      (exitAddress (command candidate)) (compiled_site _ 46 matrix)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

private theorem ternary_target_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (xs : List (Bool × Bool)) (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords Q) :
    xs.any (CodeCandidates.invalidDigit true) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : CodeCandidates.digitBits x ∈ CodeCandidates.matrixWords Q :=
    h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [CodeCandidates.ternary_digit_complete x
    (Q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) hi.symm]

/-- Actual exhaustive ternary code search with polynomial storage on the same
run. The pure existence premise is discharged for the supplied parameters
below; no evaluator, layout or successful candidate is supplied to the code. -/
theorem local_search_runs_oai (t D d A : ℕ)
    (hexists : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d)
    (a : State 16 48) (ha : LocalMatrixReady t D d a)
    (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (t * D) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin t → Fin D → SparseCode.F3), n ≤ localTime A t D d ∧
      Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d ∧
      LocalMatrixReady t D d out ∧ (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A (t * D)) ∧
      ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
        (a.withPC (some (compiled localSearch 46 18).entry)) c →
        ∀ i, (c.stacks i).length ≤ localSpace A t D d := by
  let B := boundary A (t * D)
  let Good : List Bool → Prop := fun word => ∃ Q : Fin t → Fin D → SparseCode.F3,
    word = matrixFrames Q ∧ SparseCode.HasDistance Q d
  have hB : 6 * (t * D) + 1 ≤ B := by dsimp [B, boundary]; omega
  have hcap : 5 * (t * D) ≤ B := by omega
  have hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate (t * D) 2 → (LocalMatrixReady t D d) a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ candidateBudget B (t * D) D (callbackBudget t D d) (localStreamBudget t D d) ∧ Eval localMatrixCandidate n a b ∧
        (∀ i, i ≠ 18 → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks 18)) ∧
        ∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
          (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ candidateSpace B (t * D) D (callbackBudget t D d) := by
    intro words start hw hready hb hc
    obtain ⟨n, out, hn, he, _, hf, hbound, hsound, hspace⟩ :=
      local_matrix_candidate_runs t D d start B hb hcap hready words hw hc
    exact ⟨n, out, hn, he, hf, hbound, hsound, hspace⟩
  obtain ⟨targetQ, htargetQ⟩ := hexists
  have hwidth : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  have hshape : (CodeCandidates.matrixWords targetQ).map List.length = List.replicate (t * D) 2 := by
    simpa only [hwidth] using CodeCandidates.matrixWords_shape targetQ
  have htarget : ∀ start, LocalMatrixReady t D d start →
      (∀ i, (start.stacks i).length ≤ B) →
      start.stacks 40 = Encoding.encodeList id (CodeCandidates.matrixWords targetQ) →
      ∃ n out, Eval localMatrixCandidate n start out ∧ out.regs 15 = true := by
    intro start hready hb hc
    obtain ⟨xs, _, hfields⟩ := CodeCandidates.pairs_of_shape (CodeCandidates.matrixWords targetQ)
      (t * D) hshape
    have hcurrent : start.stacks 40 = CodeCandidates.tupleBits xs := by rw [hc, tupleBits_eq, hfields]
    obtain ⟨n, out, _, he, hyes, _, _⟩ := local_matrix_candidate_valid targetQ d xs hfields
      (ternary_target_valid targetQ xs hfields) start B hb hready.work hready.rows
      hready.distance hready.dimension hready.payload hready.scratch hready.counter hready.latch
      hready.counterScratch hready.copy hcurrent hready.outerInput hready.outerPayload hready.outerScratch
    exact ⟨n, out, he, hyes.mpr htargetQ⟩
  obtain ⟨n, out, hn, he, hgood, hready, hframe, hbound, hspace⟩ := command_runs
    localMatrixCandidate 18 (by decide) (by decide) (by decide) (by decide)
    (LocalMatrixReady t D d) Good (fun _ _ h hf => h.frame hf) (fun _ h => h.outerScratch)
    (t * D) B _ _ hB hchecks (CodeCandidates.matrixWords targetQ) hshape htarget a ha
    (fun i => (hab i).trans (by dsimp [B, boundary]; omega))
    (by simp [hdim]) h40 h41 h42 ha.outerInput
  obtain ⟨Q, hmatrix, hQ⟩ := hgood
  exact ⟨n, out, Q, hn, he, hmatrix, hQ, hready, hframe, hbound, hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs_oai
