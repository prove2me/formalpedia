-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:29:54.783304+00:00
-- url     : https://prove2.me/submissions/b936d789-a665-4dab-ac04-0106f86356cb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_finalize_prefix
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumSpace_seed_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- The local routine is linear in the current word, even when its value is exponential. -/
theorem ripple_prefix_stack_bound (carry bit present flag : Bool) (word : List Bool)
    {steps : ℕ} {intermediate : Cfg 3 2 11}
    (hle : steps ≤ rippleCost carry word + 1)
    (htrace : Trace (rippleProgram carry) steps
      ((localData bit present flag word []).withPC (some (rippleProgram carry).entry))
      intermediate) (i : Fin 2) :
    (intermediate.stacks i).length ≤ 9 * word.length + 8 := by
  have hs : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hg := trace_dataBits (rippleProgram carry) htrace
  have hc := rippleCost_le carry word
  have hinit : dataBits
      ((localData bit present flag word []).withPC (some (rippleProgram carry).entry)) =
      word.length := by
    simp [dataBits, stackBits, localData,
      counterStacks, Fin.sum_univ_two]
  rw [hinit] at hg
  omega

private theorem powerTwo_scan (word output : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 2)
      (counterCfg 2 bit present flag word output)
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ output)) := by
  induction word generalizing output bit present with
  | nil =>
      exact .cons (b := counterCfg 3 false false flag [] output)
        (by simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  | cons b word ih =>
      have h := Computation.Trace.cons
        (show step powerTwoProgram (counterCfg 2 bit present flag (b :: word) output) =
          some (counterCfg 3 b true flag word output) by
            simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (Computation.Trace.cons
          (show step powerTwoProgram (counterCfg 3 b true flag word output) =
            some (counterCfg 4 b true flag word output) by
              simp [step, powerTwoProgram, counterCfg, execInstr])
          (Computation.Trace.cons
            (show step powerTwoProgram (counterCfg 4 b true flag word output) =
              some (counterCfg 5 false true flag word output) by
                simp [step, powerTwoProgram, counterCfg, execInstr])
            (Computation.Trace.cons
              (show step powerTwoProgram (counterCfg 5 false true flag word output) =
                some (counterCfg 2 false true flag word (false :: output)) by
                  simp [step, powerTwoProgram, counterCfg, execInstr])
              (ih (false :: output) false true))))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp [List.replicate_succ', List.append_assoc]

theorem powerTwo_trace (word : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 5)
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry))
      ((localData false false flag []
        (List.replicate word.length false ++ [true])).withPC none) := by
  have hstart : Trace powerTwoProgram 2 (counterCfg 0 bit present flag word [])
      (counterCfg 2 true present flag word [true]) :=
    .cons (b := counterCfg 1 true present flag word [])
      (by simp [step, powerTwoProgram, counterCfg, execInstr])
      (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  have hend : Trace powerTwoProgram 1
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ [true]))
      ((localData false false flag [] (List.replicate word.length false ++ [true])).withPC none) :=
    .cons (by simp [step, powerTwoProgram, counterCfg, execInstr, localData,
      StructuredProgram.State.withPC]) (.refl _)
  have h := (hstart.trans (powerTwo_scan word [true] true present flag)).trans hend
  have ht : 2 + (4 * word.length + 2) + 1 = 4 * word.length + 5 := by omega
  rw [ht] at h
  simpa [localData, StructuredProgram.State.withPC, counterCfg, powerTwoProgram] using h

theorem powerTwo_value (width : ℕ) :
    value (List.replicate width false ++ [true]) = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CounterLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary counted loops whose invariant couples the current cursor to
remaining fuel. The invariant is transferred through the concrete decrement
and zero test, rather than through arbitrary changes to controller words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

/-- A measured callback can establish the next boundary invariant directly.
It is required only while the actual remaining counter value is positive. -/
theorem visits_exists_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e)) (fuel : ℕ) :
    ∀ i d, value (d.stacks p.counter) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.counter)) → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + fuel) e ∧
        e.stacks p.scratch = [] ∧ costs.sum ≤ budgetSum cost i fuel := by
  induction fuel with
  | zero =>
      intro i d hv hs hf hi
      have hz : isZero (d.stacks p.counter) = true := (isZero_eq_true_iff _).2 hv
      exact ⟨[], 1, d, .done d (by simpa [hz] using hf) hv,
        by simpa using hi, hs, by simp [budgetSum]⟩
  | succ fuel ih =>
      intro i d hv hs hf hi
      have hp : 0 < value (d.stacks p.counter) := by omega
      have hz : isZero (d.stacks p.counter) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, hnb, he, hc, hes, hei⟩ := spec i d hi hs hp
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hn : value ((nextState p e).stacks p.counter) = fuel := by
        rw [nextState_counter, hc]
        have hd := value_decrement hep
        rw [hc, hv] at hd
        omega
      obtain ⟨costs, nt, f, ht, hfi, hfs, hbudget⟩ :=
        ih (i + 1) (nextState p e) hn (nextState_scratch ..) (nextState_flag ..) hei
      refine ⟨nb :: costs, (nb + advanceCost p e) + nt + 1, f,
        .step hf' hp he hc hes ht, ?_, hfs, ?_⟩
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hfi
      · simpa only [List.sum_cons, budgetSum] using Nat.add_le_add hnb hbudget

/-- The initial test is explicit. No hypothesis allows changing the counter
arbitrarily, so cursor/fuel relations and terminal width exceptions survive. -/
theorem for_correct_measured_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e))
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 (testResult p d)) :
    ∃ costs n e, Eval (forCmd p body) n d e ∧
      (∃ loopSteps, Visits p body costs loopSteps (testResult p d) e ∧
        n = (8 * (d.stacks p.counter).length + 7) + loopSteps) ∧
      costs.length = value (d.stacks p.counter) ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      costs.sum ≤ budgetSum cost 0 (value (d.stacks p.counter)) ∧
      n ≤ costs.sum + (value (d.stacks p.counter) + 1) *
        (16 * (d.stacks p.counter).length + 16) := by
  have hst := testResult_stacks p d hs
  obtain ⟨costs, nt, e, ht, hei, hes, hbudget⟩ :=
    visits_exists_next p body I cost spec (value (d.stacks p.counter)) 0
      (testResult p d) (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [testResult_flag, hst]) hi
  rcases ht.bounds with ⟨hlen, hzero, hwidth, htime⟩
  rw [hst] at hlen hwidth htime
  refine ⟨costs, (8 * (d.stacks p.counter).length + 7) + nt, e,
    .seq (test_eval p d hs) ht.eval, ⟨nt, ht, rfl⟩, hlen,
    by simpa using hei, hzero, hwidth, hes, hbudget, ?_⟩
  rw [hlen] at htime
  calc
    8 * (d.stacks p.counter).length + 7 + nt ≤
        costs.sum + value (d.stacks p.counter) *
          (16 * (d.stacks p.counter).length + 16) +
          (16 * (d.stacks p.counter).length + 16) := by omega
    _ = costs.sum + (value (d.stacks p.counter) + 1) *
        (16 * (d.stacks p.counter).length + 16) := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem copy_eval (d : Data) (src dst : Fin 896)
    (hsd : src≠dst) (hst : src≠31) (htd : (31:Fin 896)≠dst) (ht : d.stacks 31=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copyState d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

theorem clear_eval (d : Data) (src : Fin 896) :
    Eval (clear src) (2*(d.stacks src).length+3) d (clearState d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram


theorem seq_space {c e : Code} {n m B : ℕ} {a b d : Data}
    (hc : Eval c n a b) (he : Eval e m b d)
    (hcb : (∀ q z, q ≤ n → Trace (compiled c 860 860) q
      (a.withPC (some (compiled c 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) (heb : (∀ q z, q ≤ m → Trace (compiled e 860 860) q
      (b.withPC (some (compiled e 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) :
    (∀ q z, q ≤ (n+m) → Trace (compiled (.seq c e) 860 860) q
      (a.withPC (some (compiled (.seq c e) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) :=
  StructuredSpace.sequence_stack_bound hc he 860 860 hcb heb
    (compiled (.seq c e) 860 860) (siteAddress (.seq c e)) (exitAddress (.seq c e))
    (compiled_site (.seq c e) 860 860)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

theorem Cursor.initial (h : ℕ) (d : Data)
    (hw : d.stacks 859 = List.replicate h false)
    (hf : d.stacks 860 = List.replicate h false ++ [true]) (hs : d.stacks 861 = []) :
    Cursor h 0 d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hs⟩
  · simp [hw]
  · simpa [hf] using Counters.powerTwo_value h
  · simp [hf]
  · simp [hw]
  · intro _; simp [hw]

theorem power_eval (d : Data) (hf : d.stacks 860 = []) :
    Eval power (4 * (d.stacks 861).length + 5) d (powerResult d) := by
  have hr : Function.Injective powerRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective powerStacks := by decide
  have hp : projectState powerRegisters powerStacks d =
      CounterForPrograms.localData (d.regs 0) (d.regs 1) (d.regs 2)
        (d.stacks 861) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [powerStacks, counterStacks, hf]
  have ht := Counters.powerTwo_trace (d.stacks 861) (d.regs 0) (d.regs 1) (d.regs 2)
  rw [← hp] at ht
  exact eval_call_from_state Counters.powerTwoProgram powerRegisters powerStacks d hr hs ht

theorem powerResult_frame (d : Data) (j : Fin 896) (h0 : j ≠ 860) (h1 : j ≠ 861) :
    (powerResult d).stacks j = d.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  fin_cases i <;> simp_all [powerStacks]

open HeadEvaluationProgram.StagedGate (copy copyState copy_eval clear clearState clear_eval)

theorem seed_eval (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hfuel : d.stacks 860 = []) (hscratch : d.stacks 861 = [])
    (htemp : d.stacks 31 = []) :
    Eval seed (18 * h + 2 * (d.stacks 853).length + 18) d (seeded d) := by
  let d1 := copyState d 651 859
  let d2 := copyState d1 651 861
  have h1 := copy_eval d 651 859 (by decide) (by decide) (by decide) htemp
  have h2 := copy_eval d1 651 861 (by decide) (by decide) (by decide)
    (by simp [d1, copyState, StackRoutines.copyStacks, htemp])
  have h3 := power_eval d2 (by simp [d2, d1, copyState, StackRoutines.copyStacks, hfuel])
  have h4 := clear_eval (powerResult d2) 853
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  · rfl
  · simp [d2, d1, copyState, StackRoutines.copyStacks, hshape, hscratch,
      powerResult_frame _ _ (by decide : (853 : Fin 896) ≠ 860) (by decide)]
    omega
  · rfl

theorem seeded_stacks (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hcursor : d.stacks 859 = []) (hscratch : d.stacks 861 = []) :
    (seeded d).stacks = Function.update (Function.update (Function.update d.stacks
      859 (List.replicate h false)) 860 (List.replicate h false ++ [true])) 853 [] := by
  funext j
  by_cases h853 : j = 853
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks]
  by_cases h860 : j = 860
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, copyState,
      StackRoutines.copyStacks, hshape, hscratch]
  by_cases h861 : j = 861
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, hscratch]
  simp [seeded, clearState, StackRoutines.clearStacks, h853, h860,
    powerResult_frame _ j h860 h861, copyState, StackRoutines.copyStacks, h861,
    hshape, hcursor]

theorem seeded_cursor (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hcursor : d.stacks 859 = []) (hscratch : d.stacks 861 = []) :
    Cursor h 0 (seeded d) := by
  have hs := seeded_stacks d h hshape hcursor hscratch
  apply Cursor.initial
  · simp [hs]
  · simp [hs]
  · simp [hs, hscratch]


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

theorem finalize_eval (a : Data) :
    Eval finalize (2 * (a.stacks 859).length + 2 * (a.stacks 860).length + 7)
      a (finalized a) := by
  have he := eval_liftCommand_from_state (SubexpSetupStorage.clearMany [859, 860]) 859 853
    FactorEnvironment.registerMap id a (Fin.castAdd_injective _ _) Function.injective_id
    (SubexpSetupStorage.clearMany_eval [859, 860]
      (projectState FactorEnvironment.registerMap id a))
  convert he using 1
  · rfl
  · simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, projectState]
    omega
  · rfl

theorem finalized_stacks (a : Data) :
    (finalized a).stacks = Function.update (Function.update a.stacks 859 []) 860 [] := by
  funext i
  rw [show (finalized a).stacks i =
      (SubexpSetupStorage.clearManyState [859, 860]
        (projectState FactorEnvironment.registerMap id a)).stacks i from
    embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState, projectState]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Sharp storage bounds for binary head-assignment controllers. Only the
counter's retained word length enters the local controller budget; every other
caller stack retains the same envelope throughout arbitrarily many visits. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

private theorem local_call_space {R S labels steps bound : ℕ} (p : Ports R S)
    (program : Program 3 2 labels) (a : State R S) (b : State 3 2)
    (hs : a.stacks p.scratch = [])
    (hrun : Trace program steps
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry))
      (b.withPC none))
    (hlocal : ∀ q z, q ≤ steps → Trace program q
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) z →
      ∀ i, (z.stacks i).length ≤ bound)
    (hframe : ∀ i, (a.stacks i).length ≤ bound) :
    let command := Cmd.call (ProgramLinking.liftProgram program p.register (stackPorts p))
    ∀ q z, q ≤ steps → Trace (compiled command p.counter p.counter) q
      (a.withPC (some (compiled command p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  dsimp only
  have hstart : install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [] = a := by
    rw [← hs]
    exact install_self p a
  have he := eval_call_lifted program p.register (stackPorts p) a
    p.register.injective (stackPorts p).injective hrun
  change Eval (.call (ProgramLinking.liftProgram program p.register (stackPorts p))) steps
    (install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [])
    (embedState p.register (stackPorts p) a b) at he
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound program p.register (stackPorts p)
    (a.withPC none) p.register.injective (stackPorts p).injective hrun hlocal hframe
  have hinit : ProgramLinking.embedCfg p.register (stackPorts p) id none (a.withPC none)
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram program p.register (stackPorts p)).entry) := by
    change (install p a _ _ _ _ []).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call prog ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (.call (ProgramLinking.liftProgram program p.register (stackPorts p)))
          p.counter p.counter) ht hglobal

/-- Increment and decrement use only a two-stack local footprint. -/
theorem ripple_space {R S bound : ℕ} (p : Ports R S) (carry : Bool) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    let command := Cmd.call (ProgramLinking.liftProgram (rippleProgram carry)
      p.register (stackPorts p))
    ∀ q z, q ≤ rippleCost carry (a.stacks p.counter) + 1 →
      Trace (compiled command p.counter p.counter) q
        (a.withPC (some (compiled command p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  apply local_call_space p (rippleProgram carry) a _ hs
    (ripple_local_trace carry _ _ _ (a.stacks p.counter)) _ hframe
  intro q z hq hz i
  exact (Counters.ripple_prefix_stack_bound carry _ _ _ (a.stacks p.counter) hq hz i).trans
    hbudget

/-- The restoring zero test has the same bound independently of its counter value. -/
theorem zero_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 6 →
      Trace (compiled (zeroCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (zeroCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  apply local_call_space p zeroProgram a _ hs
    (zero_local_trace _ _ _ (a.stacks p.counter)) _ hframe
  intro q z hq hz i
  have hsize : dataBits ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some zeroProgram.entry)) ≤
      (a.stacks p.counter).length := by
    simp [dataBits, stackBits, localData, counterStacks, Fin.sum_univ_two]
  have hg := StructuredSpace.local_stack_bound zeroProgram hsize q z hq hz i
  omega

/-- Adding the one Boolean negation changes no stack. -/
theorem test_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 7 →
      Trace (compiled (testCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (testCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have he := zero_eval p a hs
  have hfirst := zero_space p a hs hframe hbudget
  have hmiddle := hfirst _ _ le_rfl (compiled_trace he p.counter p.counter)
  have hnot := Eval.base (StructuredProgram.Eval.atom
    (.bnot (p.register 2) (p.register 2)) (zeroResult p a))
  have hsecond : ∀ q z, q ≤ 1 →
      Trace (compiled (.base (.atom (.bnot (p.register 2) (p.register 2))))
        p.counter p.counter) q ((zeroResult p a).withPC (some
          (compiled (.base (.atom (.bnot (p.register 2) (p.register 2))))
            p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
    intro q z hq hz
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with rfl | rfl
    · cases hz
      exact hmiddle
    · rw [trace_same_length_unique hz (compiled_trace hnot p.counter p.counter)]
      exact hmiddle
  have whole := StructuredSpace.sequence_stack_bound he hnot p.counter p.counter hfirst
    hsecond (compiled (testCmd p) p.counter p.counter) (siteAddress (testCmd p))
    (exitAddress (testCmd p)) (compiled_site (testCmd p) p.counter p.counter)
  simpa only [StructuredCalls.compiled, Nat.add_assoc] using whole

/-- The complete countdown transition preserves one caller envelope. -/
theorem advance_space {R S bound : ℕ} (p : Ports R S) (a : State R S)
    (hs : a.stacks p.scratch = []) (hp : 0 < value (a.stacks p.counter))
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 9 * (a.stacks p.counter).length + 8 ≤ bound) :
    ∀ q z, q ≤ advanceCost p a →
      Trace (compiled (advanceCmd p) p.counter p.counter) q
        (a.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have he := decrement_eval p a hs
  have hfirst := ripple_space p false a hs hframe hbudget
  have hmiddle := hfirst _ _ le_rfl (compiled_trace he p.counter p.counter)
  have hbudget' : 9 * ((decrementResult p a).stacks p.counter).length + 8 ≤ bound := by
    rw [decrementResult_counter, decrement_length hp]
    exact hbudget
  have whole := StructuredSpace.sequence_stack_bound he
    (test_eval p (decrementResult p a) (decrementResult_scratch p a))
    p.counter p.counter hfirst
    (test_space p (decrementResult p a) (decrementResult_scratch p a) hmiddle hbudget')
    (compiled (advanceCmd p) p.counter p.counter) (siteAddress (advanceCmd p))
    (exitAddress (advanceCmd p)) (compiled_site (advanceCmd p) p.counter p.counter)
  simpa only [StructuredCalls.compiled, advanceCost, decrementResult_counter] using whole


/-- Every binary-counted visit keeps one fixed bound, including caller frames.
Only the counter word width enters the controller-local side condition. -/
theorem visits_space_next {R S bound width : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hwidth : ∀ i d, I i d → (d.stacks p.counter).length ≤ width)
    (hbudget : 9 * width + 8 ≤ bound)
    (hnext : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      I (i + 1) (nextState p e))
    (hcallback : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      ∀ q z, q ≤ nb → Trace (compiled body p.counter p.counter) q
        (d.withPC (some (compiled body p.counter p.counter).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    {costs : List ℕ} {steps i : ℕ} {a b : State R S}
    (hvis : Visits p body costs steps a b) (hI : I i a) (hs : a.stacks p.scratch = []) :
    ∀ q z, q ≤ steps → Trace (compiled (loopCmd p body) p.counter p.counter) q
      (a.withPC (some (compiled (loopCmd p body) p.counter p.counter).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  induction hvis generalizing i with
  | done a hf hz =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf (hbound i a hI)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step a middle b nb nt costs hf hp hb hc hscratch tail ih =>
      have hbody := hcallback i a middle nb hI hs hp hb
      have hmiddle := hbody _ _ le_rfl (compiled_trace hb p.counter p.counter)
      have hpositive : 0 < value (middle.stacks p.counter) := by simpa only [hc] using hp
      have hlocal : 9 * (middle.stacks p.counter).length + 8 ≤ bound := by
        rw [hc]
        have hw := hwidth i a hI
        omega
      have hcontrol := advance_space p middle hscratch hpositive hmiddle hlocal
      have ha := advance_eval p middle hscratch
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hbody hcontrol (compiled (.seq body (advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (advanceCmd p))) (exitAddress (.seq body (advanceCmd p)))
        (compiled_site (.seq body (advanceCmd p)) p.counter p.counter)
      have hafter := hnext i a middle nb hI hs hp hb
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter (nextState_scratch p middle))
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The initial restoring test and final halt preserve the same bound too. -/
theorem for_space_next {R S bound width : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hwidth : ∀ i d, I i d → (d.stacks p.counter).length ≤ width)
    (hbudget : 9 * width + 8 ≤ bound)
    (hnext : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      I (i + 1) (nextState p e))
    (hcallback : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      ∀ q z, q ≤ nb → Trace (compiled body p.counter p.counter) q
        (d.withPC (some (compiled body p.counter p.counter).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    {costs : List ℕ} {steps : ℕ} {a b : State R S}
    (hs : a.stacks p.scratch = [])
    (hI : I 0 (testResult p a))
    (hvis : Visits p body costs steps (testResult p a) b) :
    ∀ q z, q ≤ 8 * (a.stacks p.counter).length + 7 + steps + 1 →
      Trace (compiled (forCmd p body) p.counter p.counter) q
        (a.withPC (some (compiled (forCmd p body) p.counter p.counter).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  have hst := testResult_stacks p a hs
  have hframe : ∀ j, (a.stacks j).length ≤ bound := by
    simpa only [hst] using hbound 0 (testResult p a) hI
  have hw : (a.stacks p.counter).length ≤ width := by
    simpa only [hst] using hwidth 0 (testResult p a) hI
  have htest := test_eval p a hs
  have hfirst := test_space p a hs hframe (by omega)
  have hloop := visits_space_next p body I hbound hwidth hbudget hnext hcallback hvis hI
    (by simpa only [hst] using hs)
  have hseq := StructuredSpace.sequence_stack_bound htest hvis.eval p.counter p.counter
    hfirst hloop (compiled (forCmd p body) p.counter p.counter)
    (siteAddress (forCmd p body)) (exitAddress (forCmd p body))
    (compiled_site (forCmd p body) p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq htest hvis.eval)
    p.counter p.counter hseq


open HeadEvaluationProgram.StagedGate

/-- Relational dictionary invariants pass through the actual complete scan.
The invariant may contain existential representations and decoded partial sums;
no canonical executable evaluator is assumed. -/
theorem scan_resources_oai (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded a))) :
    ∃ steps e,
      Trace (HeadSumProgram.scanProgram accepted) steps
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.scanProgram accepted) q
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hseed := HeadSumProgram.seed_eval a h hshape hfuel hscratch htemp
  have hseedPrefix := seed_space hseed hcursor hfuel hscratch htemp hframe (by
    rw [hshape, List.length_replicate]
    omega)
  have hseedCursor := HeadSumProgram.seeded_cursor a h hshape hcursor hscratch
  have hs : (HeadSumProgram.seeded a).stacks 861 = [] := hseedCursor.scratch
  have hf : value ((HeadSumProgram.seeded a).stacks 860) = 2 ^ h := by
    have hf := hseedCursor.fuel
    omega
  have hw : ((HeadSumProgram.seeded a).stacks 860).length = h + 1 := hseedCursor.fuelWidth
  obtain ⟨costs, nt, e, he, hvisit, _, hI, _, _, hes, hsum, htime⟩ :=
    CounterLoops.for_correct_measured_next HeadSumProgram.fuelPorts
      (HeadSumProgram.body accepted) I (fun _ => cost) spec
      (HeadSumProgram.seeded a) hs hi
  obtain ⟨loopSteps, hvis, heq⟩ := hvisit
  change nt = 8 * ((HeadSumProgram.seeded a).stacks 860).length + 7 + loopSteps at heq
  have hnext : ∀ i d e nb, I i d → d.stacks HeadSumProgram.fuelPorts.scratch = [] →
      0 < value (d.stacks HeadSumProgram.fuelPorts.counter) →
      Eval (HeadSumProgram.body accepted) nb d e →
      I (i + 1) (nextState HeadSumProgram.fuelPorts e) := by
    intro i d e nb hd hds hp hEval
    obtain ⟨nc, f, _, hEval', _, _, hnext⟩ := spec i d hd hds hp
    have hequal : e = f := Eval.final_unique (860 : Fin 896) hEval hEval'
    subst f
    exact hnext
  have hloopPrefix := for_space_next HeadSumProgram.fuelPorts (HeadSumProgram.body accepted) I
    hbound (fun i d hd => (hcursorI i d hd).fuelWidth.le) hbudget hnext hcallback hs hi hvis
  have hloop : ∀ q z, q ≤ nt → Trace (compiled (HeadSumProgram.command accepted) 860 860) q
      ((HeadSumProgram.seeded a).withPC
        (some (compiled (HeadSumProgram.command accepted) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
    intro q z hq hz
    exact hloopPrefix q z (by
      change q ≤ 8 * ((HeadSumProgram.seeded a).stacks 860).length + 7 + loopSteps + 1
      omega) hz
  have hmiddle := hloop _ _ le_rfl (compiled_trace he 860 860)
  have hfinal := HeadSumProgram.finalize_eval e
  have hfinalPrefix := HeadSumProgram.finalize_prefix hfinal hmiddle
  have htail := seq_space he hfinal hloop hfinalPrefix
  have hfull := StructuredSpace.sequence_stack_bound hseed (he.seq hfinal) 860 860
    hseedPrefix htail (HeadSumProgram.scanProgram accepted)
    (siteAddress (HeadSumProgram.scan accepted)) (exitAddress (HeadSumProgram.scan accepted))
    (compiled_site (HeadSumProgram.scan accepted) 651 853)
  have hwhole := hseed.seq (he.seq hfinal)
  have hfinalCursor := hcursorI _ e hI
  have hcursorWidth := hfinalCursor.wordWidth
  have hfuelWidth := hfinalCursor.fuelWidth
  have hloopTime : nt + 1 ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) := by
    simp only [HeadSumProgram.fuelPorts, budgetSum_const, hf, hw] at hsum htime
    nlinarith
  have hsumLength := hframe 853
  refine ⟨_, e, compiled_halt_trace hwhole 651 853,
    by simpa only [HeadSumProgram.fuelPorts, hf] using hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [HeadSumProgram.finalized_stacks]
  · simp [HeadSumProgram.finalized_stacks]
  · simp [HeadSumProgram.finalized_stacks]
  · simpa [HeadSumProgram.fuelPorts, HeadSumProgram.finalized_stacks] using hes
  · omega
  · exact StructuredSpace.compiled_halt_stack_bound hwhole 651 853 hfull


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources_oai
