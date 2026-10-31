-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:36:14.223365+00:00
-- url     : https://prove2.me/submissions/ed5b6540-4fa7-4bfc-8895-a5c009f5bedb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S169
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

theorem restore_trace (input scratch : List Bool) (v present carry : Bool) :
    Trace program (3 * scratch.length + 3)
      (cfg (some 14) v present carry input scratch)
      (cfg none false false carry (scratch.reverse ++ input) []) := by
  have ht := StackRoutines.transfer_trace program (1 : Fin 2) 0 (0 : Fin 3) 1
    14 15 16 17 (by decide) (by decide) rfl rfl rfl
    (counterRegs v present carry) (counterStacks input scratch)
  have hs : StackRoutines.transferStacks (1 : Fin 2) 0 (counterStacks input scratch) =
      counterStacks (scratch.reverse ++ input) [] := by
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks, counterStacks]
  have hr : readRegs (counterRegs v present carry) 0 1 none =
      counterRegs false false carry := by simp [readRegs]
  have ht' : Trace program (3 * scratch.length + 2)
      (cfg (some 14) v present carry input scratch)
      (cfg (some 17) false false carry (scratch.reverse ++ input) []) := by
    simpa [cfg, StackRoutines.transferResult, hs, hr] using ht
  have hh : Trace program 1
      (cfg (some 17) false false carry (scratch.reverse ++ input) [])
      (cfg none false false carry (scratch.reverse ++ input) []) :=
    .cons (by simp [step, cfg, execInstr]) (.refl _)
  simpa [Nat.add_assoc] using ht'.trans hh

theorem word_bit_trace (b v present : Bool) (input scratch : List Bool) :
    Trace program 7
      (cfg (some 4) v present true (true :: b :: input) scratch)
      (cfg (some (if b then 4 else 11)) (!b) true true input ((!b) :: true :: scratch)) := by
  have h0 : step program (cfg (some 4) v present true (true :: b :: input) scratch) =
      some (cfg (some 5) true true true (b :: input) scratch) := by
    simp [step, cfg, execInstr, readRegs]
  have h1 : step program (cfg (some 5) true true true (b :: input) scratch) =
      some (cfg (some 6) true true true (b :: input) scratch) := by
    simp [step, cfg, execInstr]
  have h2 : step program (cfg (some 6) true true true (b :: input) scratch) =
      some (cfg (some 7) true true true (b :: input) (true :: scratch)) := by
    simp [step, cfg, execInstr]
  have h3 : step program (cfg (some 7) true true true (b :: input) (true :: scratch)) =
      some (cfg (some 8) b true true input (true :: scratch)) := by
    simp [step, cfg, execInstr, readRegs]
  have h4 : step program (cfg (some 8) b true true input (true :: scratch)) =
      some (cfg (some 9) (!b) true true input (true :: scratch)) := by
    simp [step, cfg, execInstr]
  have h5 : step program (cfg (some 9) (!b) true true input (true :: scratch)) =
      some (cfg (some 10) (!b) true true input ((!b) :: true :: scratch)) := by
    simp [step, cfg, execInstr]
  have h6 : step program (cfg (some 10) (!b) true true input ((!b) :: true :: scratch)) =
      some (cfg (some (if b then 4 else 11)) (!b) true true input ((!b) :: true :: scratch)) := by
    cases b <;> simp [step, cfg, execInstr]
  exact .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.refl _)))))))

theorem frame_end_trace (v present : Bool) (input scratch : List Bool) :
    Trace program 3
      (cfg (some 4) v present true (false :: input) scratch)
      (cfg (some 1) false true true input (false :: scratch)) := by
  refine .cons (b := cfg (some 5) false true true input scratch) ?_
    (.cons (b := cfg (some 12) false true true input scratch) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, cfg, execInstr, readRegs]

theorem record_start_trace (v present : Bool) (input scratch : List Bool) :
    Trace program 3
      (cfg (some 1) v present true (true :: input) scratch)
      (cfg (some 4) true true true input (true :: scratch)) := by
  refine .cons (b := cfg (some 2) true true true input scratch) ?_
    (.cons (b := cfg (some 3) true true true input scratch) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, cfg, execInstr, readRegs]

theorem list_end_trace (v present : Bool) (input scratch : List Bool) :
    Trace program (3 * scratch.length + 9)
      (cfg (some 1) v present true (false :: input) scratch)
      (cfg none false false true (scratch.reverse ++ false :: input) []) := by
  have hp : Trace program 3
      (cfg (some 1) v present true (false :: input) scratch)
      (cfg (some 14) false true true input (false :: scratch)) := by
    refine .cons (b := cfg (some 2) false true true input scratch) ?_
      (.cons (b := cfg (some 13) false true true input scratch) ?_ (.cons ?_ (.refl _)))
    all_goals simp [step, cfg, execInstr, readRegs]
  have h := hp.trans (restore_trace input (false :: scratch) false true true)
  have ht : 3 + (3 * (false :: scratch).length + 3) = 3 * scratch.length + 9 := by
    simp only [List.length_cons]
    omega
  rw [ht] at h
  simpa [List.reverse_cons, List.append_assoc] using h

/-- If a component is exhausted, scanning continues at the next record. -/
theorem frame_carry_trace (word rest scratch : List Bool) (v present : Bool)
    (hcarry : (bumpWord word).1 = true) :
    Trace program (7 * word.length + 3)
      (cfg (some 4) v present true (Encoding.frame word ++ rest) scratch)
      (cfg (some 1) false true true rest
        ((Encoding.frame (bumpWord word).2).reverse ++ scratch)) := by
  induction word generalizing v present scratch with
  | nil => simpa [Encoding.frame, bumpWord] using frame_end_trace v present rest scratch
  | cons b bs ih =>
    cases b with
    | false => simp [bumpWord] at hcarry
    | true =>
      have hc : (bumpWord bs).1 = true := hcarry
      have hp := word_bit_trace true v present (Encoding.frame bs ++ rest) scratch
      have hi := ih (false :: true :: scratch) false true hc
      simpa [Encoding.frame, bumpWord, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.trans hi

/-- Once a zero payload bit is found, the finite program restores the entire
scanned prefix and returns without reading later payloads. -/
theorem frame_stop_runs (word rest scratch : List Bool) (v present : Bool)
    (hcarry : (bumpWord word).1 = false) :
    RunsIn program (13 * word.length + 3 * scratch.length + 4)
      (cfg (some 4) v present true (Encoding.frame word ++ rest) scratch)
      (cfg none false false false
        (scratch.reverse ++ Encoding.frame (bumpWord word).2 ++ rest) []) := by
  induction word generalizing v present scratch with
  | nil => simp [bumpWord] at hcarry
  | cons b bs ih =>
    cases b with
    | false =>
      have hp := word_bit_trace false v present (Encoding.frame bs ++ rest) scratch
      have hm : Trace program 1
          (cfg (some 11) true true true (Encoding.frame bs ++ rest) (true :: true :: scratch))
          (cfg (some 14) true true false (Encoding.frame bs ++ rest) (true :: true :: scratch)) :=
        .cons (by simp [step, cfg, execInstr]) (.refl _)
      have hr := restore_trace (Encoding.frame bs ++ rest) (true :: true :: scratch)
        true true false
      refine ⟨7 + 1 + (3 * (true :: true :: scratch).length + 3), ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa [Encoding.frame, bumpWord, List.reverse_cons, List.append_assoc] using
          (hp.trans hm).trans hr
    | true =>
      have hc : (bumpWord bs).1 = false := hcarry
      have hp := word_bit_trace true v present (Encoding.frame bs ++ rest) scratch
      have hi := ih (false :: true :: scratch) false true hc
      have hp' : RunsIn program 7
          (cfg (some 4) v present true (true :: true :: (Encoding.frame bs ++ rest)) scratch)
          (cfg (some 4) false true true (Encoding.frame bs ++ rest) (false :: true :: scratch)) :=
        ⟨7, le_rfl, hp⟩
      have hrun := (hp'.trans hi).mono
        (show 7 + (13 * bs.length + 3 * (false :: true :: scratch).length + 4) ≤
          13 * (true :: bs).length + 3 * scratch.length + 4 by
          simp only [List.length_cons]
          omega)
      simpa [Encoding.frame, bumpWord, List.reverse_cons, List.append_assoc] using hrun

/-- Full framed traversal. A pre-existing reversed prefix on scratch is also
restored, so this theorem composes directly with the record-entry transition. -/
theorem list_runs (words : List (List Bool)) (rest scratch : List Bool) (v present : Bool) :
    RunsIn program (7 * (Encoding.encodeList id words).length + 3 * scratch.length + 2)
      (cfg (some 1) v present true (Encoding.encodeList id words ++ rest) scratch)
      (cfg none false false (bumpWords words).1
        (scratch.reverse ++ Encoding.encodeList id (bumpWords words).2 ++ rest) []) := by
  induction words generalizing scratch v present with
  | nil =>
    refine ⟨3 * scratch.length + 9, ?_, ?_⟩
    · simp [Encoding.encodeList]
      omega
    · simpa [Encoding.encodeList, bumpWords, List.append_assoc] using
        list_end_trace v present rest scratch
  | cons word words ih =>
    have hp : Trace program 3
        (cfg (some 1) v present true (Encoding.encodeList id (word :: words) ++ rest) scratch)
        (cfg (some 4) true true true
          (Encoding.frame word ++ (Encoding.encodeList id words ++ rest)) (true :: scratch)) := by
      simpa [Encoding.encodeList, List.append_assoc] using
        record_start_trace v present (Encoding.frame word ++ (Encoding.encodeList id words ++ rest)) scratch
    cases hc : (bumpWord word).1 with
    | false =>
      have hf := frame_stop_runs word (Encoding.encodeList id words ++ rest)
        (true :: scratch) true true hc
      have hp' : RunsIn program 3
          (cfg (some 1) v present true (Encoding.encodeList id (word :: words) ++ rest) scratch)
          (cfg (some 4) true true true
            (Encoding.frame word ++ (Encoding.encodeList id words ++ rest)) (true :: scratch)) :=
        ⟨3, le_rfl, hp⟩
      have hb : 3 + (13 * word.length + 3 * (true :: scratch).length + 4) ≤
          7 * (Encoding.encodeList id (word :: words)).length + 3 * scratch.length + 2 := by
        simp only [Encoding.encodeList, List.length_cons, List.length_append,
          Encoding.length_frame, id_eq]
        omega
      simpa [bumpWords, hc, Encoding.encodeList, List.reverse_cons, List.append_assoc] using
        (hp'.trans hf).mono hb
    | true =>
      have hf := frame_carry_trace word (Encoding.encodeList id words ++ rest)
        (true :: scratch) true true hc
      have hi := ih ((Encoding.frame (bumpWord word).2).reverse ++ true :: scratch) false true
      have hp' : RunsIn program (3 + (7 * word.length + 3))
          (cfg (some 1) v present true (Encoding.encodeList id (word :: words) ++ rest) scratch)
          (cfg (some 1) false true true (Encoding.encodeList id words ++ rest)
            ((Encoding.frame (bumpWord word).2).reverse ++ true :: scratch)) :=
        ⟨_, le_rfl, hp.trans hf⟩
      have hb : (3 + (7 * word.length + 3)) +
          (7 * (Encoding.encodeList id words).length +
            3 * ((Encoding.frame (bumpWord word).2).reverse ++ true :: scratch).length + 2) ≤
          7 * (Encoding.encodeList id (word :: words)).length + 3 * scratch.length + 2 := by
        simp only [Encoding.encodeList, List.length_cons, List.length_append,
          List.length_reverse, Encoding.length_frame, bumpWord_length, id_eq]
        omega
      simpa [bumpWords, hc, Encoding.encodeList, List.reverse_append,
        List.reverse_cons, List.append_assoc] using (hp'.trans hi).mono hb

/-- One complete invocation of the fixed table. The suffix is untouched and
the scratch stack is cleared. The bound counts actual bit-program instructions. -/
theorem increment_runs (words : List (List Bool)) (rest : List Bool)
    (v present carry : Bool) :
    RunsIn program (7 * (Encoding.encodeList id words).length + 3)
      (cfg (some 0) v present carry (Encoding.encodeList id words ++ rest) [])
      (cfg none false false (bumpWords words).1
        (Encoding.encodeList id (bumpWords words).2 ++ rest) []) := by
  have hp : Trace program 1
      (cfg (some 0) v present carry (Encoding.encodeList id words ++ rest) [])
      (cfg (some 1) v present true (Encoding.encodeList id words ++ rest) []) :=
    .cons (by simp [step, cfg, execInstr]) (.refl _)
  have hp' : RunsIn program 1
      (cfg (some 0) v present carry (Encoding.encodeList id words ++ rest) [])
      (cfg (some 1) v present true (Encoding.encodeList id words ++ rest) []) :=
    ⟨1, le_rfl, hp⟩
  have h := hp'.trans (list_runs words rest [] v present)
  have hc : 1 + (7 * (Encoding.encodeList id words).length + 3 * ([] : List Bool).length + 2) =
      7 * (Encoding.encodeList id words).length + 3 := by simp; omega
  rw [hc] at h
  simpa using h

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

theorem increment_eval (p : Ports R S) (words : List (List Bool)) (d : Data R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = []) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 3 ∧
      StructuredCalls.Eval (incrementCmd p) n d (incrementResult p d words) := by
  obtain ⟨n, hn, ht⟩ := ExecCNFTupleOdometer.increment_runs words []
    (d.regs (p.register 0)) (d.regs (p.register 1)) (d.regs (p.register 2))
  have ht' : Trace ExecCNFTupleOdometer.program n
      ((CounterForPrograms.localData (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) (Encoding.encodeList id words) []).withPC
          (some ExecCNFTupleOdometer.program.entry))
      ((CounterForPrograms.localData false false (bumpWords words).1
        (Encoding.encodeList id (bumpWords words).2) []).withPC none) := by
    simpa [ExecCNFTupleOdometer.cfg, CounterForPrograms.localData, State.withPC] using ht
  have he := StructuredCalls.eval_call_lifted ExecCNFTupleOdometer.program
    p.register (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective ht'
  change StructuredCalls.Eval (incrementCmd p) n
    (CounterForPrograms.install p d _ _ _ (Encoding.encodeList id words) [])
    (incrementResult p d words) at he
  rw [← hc, ← hs, CounterForPrograms.install_self] at he
  exact ⟨n, hn, he⟩

theorem advanceResult_outside (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    CounterForPrograms.OutsideEq p d (advanceResult p d words) := by
  intro j hc hs
  change d.stacks j = (incrementResult p d words).stacks j
  exact (CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hs).symm

theorem bumpWords_encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id (bumpWords words).2).length =
      (Encoding.encodeList id words).length := by
  have hlen : (bumpWords words).2.length = words.length := by
    simpa only [List.length_map] using congrArg List.length (bumpWords_lengths words)
  simp only [encoded_length, bumpWords_flatten_length, hlen]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Separate the retained caller envelope from each physical local input cap.
The local transient bound is never recycled as the next iteration's input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter

theorem lifted_call_bound {r s l R S : ℕ}
    (p : Program r s l) (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (a : State R S) (d e : State r s) (hproject : projectState reg stk a=d)
    (steps bound : ℕ) (ht : Trace p steps (d.withPC (some p.entry)) (e.withPC none))
    (hlocal : ∀ (q : ℕ) z, q ≤ steps → Trace p q (d.withPC (some p.entry)) z →
      ∀ i, (z.stacks i).length≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) (input output : Fin S) :
    ∀ (q : ℕ) z, q ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output) q
        (a.withPC (some (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have hstart : embedState reg stk a d=a := by rw [←hproject,embedState_project reg stk a hr hs]
  have he := eval_call_lifted p reg stk a hr hs ht
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound p reg stk (a.withPC none) hr hs ht hlocal hb
  have hinit : ProgramLinking.embedCfg reg stk id none (a.withPC none) (d.withPC (some p.entry)) =
      a.withPC (some (ProgramLinking.liftProgram p reg stk).entry) := by
    change (embedState reg stk a d).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call routine ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (ProgramLinking.liftProgram p reg stk)) input output) ht hglobal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

open HashGreedyProgram.NativeRound

/-- A complete current high tuple has linear physical length, even when its
numeric value is exponentially large. -/
theorem counter_length {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) :
    (Encoding.encodeList id words).length=4*H.card+1 := by
  rw [Enumerators.encoded_shape_length hshape]
  simp
  omega

/-- One real odometer step restores the same compact boundary. -/
theorem advance_boundary {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) (a : Data) (B : ℕ)
    (hwidth : 4*H.card+1 ≤ B) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((ExecCNFTupleEnumeration.advanceResult highPorts.counter a words).stacks i).length ≤ B := by
  intro i
  by_cases hc : i=789
  · subst i
    rw [show (789 : Fin 896)=highPorts.counter.counter from rfl,
      ExecCNFTupleEnumeration.advanceResult_counter,
      ExecCNFTupleEnumeration.bumpWords_encoded_length,counter_length H words hshape]
    exact hwidth
  · by_cases hs : i=790
    · subst i
      rw [show (790 : Fin 896)=highPorts.counter.scratch from rfl,
        ExecCNFTupleEnumeration.advanceResult_scratch]
      exact Nat.zero_le _
    · rw [←ExecCNFTupleEnumeration.advanceResult_outside highPorts.counter a words i hc hs]
      exact hB i

/-- The actual high odometer has only two local stack words. Its complete
prefix bound is a maximum with retained storage; the number of high assignments
never enters this local space estimate. -/
theorem advance_resources_oai {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) (a : Data) (B : ℕ)
    (hc : a.stacks 789=Encoding.encodeList id words) (hs : a.stacks 790=[])
    (hwidth : 4*H.card+1 ≤ B) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps, steps ≤ 28*H.card+11 ∧
      Eval (ExecCNFTupleEnumeration.advanceCmd highPorts.counter) steps a
        (ExecCNFTupleEnumeration.advanceResult highPorts.counter a words) ∧
      (∀ i, ((ExecCNFTupleEnumeration.advanceResult highPorts.counter a words).stacks i).length ≤ B) ∧
      StageSpace (ExecCNFTupleEnumeration.advanceCmd highPorts.counter) (steps+1) a
        (max (40*(H.card+1)) B) := by
  let p := highPorts.counter
  let localStart := CounterForPrograms.localData (a.regs (p.register 0))
    (a.regs (p.register 1)) (a.regs (p.register 2)) (Encoding.encodeList id words) []
  have hproject : projectState p.register (CounterForPrograms.stackPorts p) a = localStart := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [CounterForPrograms.stackPorts, p, highPorts, hc, hs]
  obtain ⟨incSteps,hincTime,ht⟩ := ExecCNFTupleOdometer.increment_runs words []
    (a.regs (p.register 0)) (a.regs (p.register 1)) (a.regs (p.register 2))
  have hlocalTrace : Trace ExecCNFTupleOdometer.program incSteps
      (localStart.withPC (some ExecCNFTupleOdometer.program.entry))
      ((CounterForPrograms.localData false false (ExecCNFTupleOdometer.bumpWords words).1
        (Encoding.encodeList id (ExecCNFTupleOdometer.bumpWords words).2) []).withPC none) := by
    simpa [ExecCNFTupleOdometer.cfg,CounterForPrograms.localData,
      StructuredProgram.State.withPC,localStart] using ht
  have hlocalSize : dataBits (localStart.withPC (some ExecCNFTupleOdometer.program.entry)) ≤
      2*(4*H.card+1) := by
    apply StreamResources.dataBits_le_mul
    intro i
    fin_cases i <;> simp [localStart, CounterForPrograms.localData,
      counter_length H words hshape]
  have hincTime' : incSteps ≤ 28*H.card+10 := by
    rw [counter_length H words hshape] at hincTime
    omega
  have hlocal : ∀ t z, t ≤ incSteps → Trace ExecCNFTupleOdometer.program t
      (localStart.withPC (some ExecCNFTupleOdometer.program.entry)) z →
      ∀ i, (z.stacks i).length ≤ max (40*(H.card+1)) B := by
    intro t z htle hz i
    have hb := StructuredSpace.local_stack_bound ExecCNFTupleOdometer.program
      (steps:=28*H.card+10) hlocalSize t z (htle.trans hincTime') hz i
    exact hb.trans ((show 2*(4*H.card+1)+(28*H.card+10) ≤ 40*(H.card+1) by omega).trans
      (Nat.le_max_left _ _))
  have hp := HighQuerySpace.lifted_call_bound ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p) p.register.injective
    (CounterForPrograms.stackPorts p).injective a localStart _ hproject incSteps
    (max (40*(H.card+1)) B) hlocalTrace hlocal
    (fun i => (hB i).trans (Nat.le_max_right _ _)) 778 777
  obtain ⟨actualInc,hactualTime,hi⟩ := ExecCNFTupleEnumeration.increment_eval p words a hc hs
  have hcall := eval_call_from_state ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p) a p.register.injective
    (CounterForPrograms.stackPorts p).injective (by rw [hproject]; exact hlocalTrace)
  have hsame : actualInc=incSteps := StreamResources.eval_steps_eq 778 777 hi hcall
  have hincSpace : StageSpace (ExecCNFTupleEnumeration.incrementCmd p) actualInc a
      (max (40*(H.card+1)) B) := by
    constructor
    simpa only [hsame] using hp
  have hnot : Eval (.base (.atom (.bnot (p.register 2) (p.register 2)))) 1
      (ExecCNFTupleEnumeration.incrementResult p a words)
      (ExecCNFTupleEnumeration.advanceResult p a words) := .base (.atom _ _)
  have hnotSpace : StageSpace (.base (.atom (.bnot (p.register 2) (p.register 2)))) 1
      (ExecCNFTupleEnumeration.incrementResult p a words) (max (40*(H.card+1)) B) := by
    constructor
    intro t z htle hz i
    have hbound : ((ExecCNFTupleEnumeration.incrementResult p a words).stacks i).length ≤ B :=
      advance_boundary H words hshape a B hwidth hB i
    have ht : t=0 ∨ t=1 := by omega
    rcases ht with rfl|rfl
    · cases hz
      exact hbound.trans (Nat.le_max_right _ _)
    · rw [trace_same_length_unique hz (compiled_trace hnot 778 777)]
      exact hbound.trans (Nat.le_max_right _ _)
  have he := hi.seq hnot
  have hprefix := StageSpace.seq hi hnot hincSpace hnotSpace
  refine ⟨actualInc+1,by omega,he,advance_boundary H words hshape a B hwidth hB,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hprefix.bound⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources_oai
