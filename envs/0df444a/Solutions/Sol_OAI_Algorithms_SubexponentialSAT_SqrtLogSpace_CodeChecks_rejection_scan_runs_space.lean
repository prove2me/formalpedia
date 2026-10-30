-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:04:10.215334+00:00
-- url     : https://prove2.me/submissions/b48895ac-0133-4ec5-9475-694291148768

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S114
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

theorem advance_eval (p : Ports R S) (words : List (List Bool)) (d : Data R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = []) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 4 ∧
      StructuredCalls.Eval (advanceCmd p) n d (advanceResult p d words) := by
  obtain ⟨n, hn, he⟩ := increment_eval p words d hc hs
  exact ⟨n + 1, by omega, .seq he (.base (.atom _ _))⟩

theorem advanceResult_outside (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    CounterForPrograms.OutsideEq p d (advanceResult p d words) := by
  intro j hc hs
  change d.stacks j = (incrementResult p d words).stacks j
  exact (CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hs).symm

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body shape ranks n d e) :
    StructuredCalls.Eval (loopCmd p body) n d e := by
  induction h with
  | done d hf => exact .while_false hf
  | step hf hw hc hb he ha tail ih => exact .while_true hf (.seq hb ha) ih

theorem bumpWords_encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id (bumpWords words).2).length =
      (Encoding.encodeList id words).length := by
  have hlen : (bumpWords words).2.length = words.length := by
    simpa only [List.length_map] using congrArg List.length (bumpWords_lengths words)
  simp only [encoded_length, bumpWords_flatten_length, hlen]

/-- Every remaining payload rank is visited exactly once. The induction is on
the semantic remaining count; that number does not occur in executable code. -/
theorem loop_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget) (fuel : ℕ) :
    ∀ (words : List (List Bool)) (d : Data R S), words.map List.length = shape → I d →
      d.stacks p.counter = Encoding.encodeList id words → d.stacks p.scratch = [] →
      d.regs (p.register 2) = true →
      CounterPrograms.value words.flatten + fuel = 2 ^ words.flatten.length →
      ∃ n e, Visits p body shape (List.range' (CounterPrograms.value words.flatten) fuel) n d e ∧
        I e ∧ e.regs (p.register 2) = false ∧ e.stacks p.scratch = [] ∧
        n ≤ fuel * (budget + 7 * (Encoding.encodeList id words).length + 5) + 1 := by
  induction fuel with
  | zero =>
    intro words d hshape hi hc hs hf hremaining
    have hlt := value_lt_power_length words.flatten
    omega
  | succ fuel ih =>
    intro words d hshape hi hc hs hf hremaining
    obtain ⟨nb, e, hnb, hbody, he, hes, hei⟩ := spec words d hshape hi hc hs
    obtain ⟨na, hna, hstep⟩ := advance_eval p words e he hes
    have hni : I (advanceResult p e words) :=
      stable 0 e (advanceResult p e words) (advanceResult_outside p e words) hei
    by_cases hz : fuel = 0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten + 1 = 2 ^ words.flatten.length := by
        simpa using hremaining
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : (advanceResult p e words).regs (p.register 2) = false := by
        simp only [advanceResult_flag, hcarry, Bool.not_true]
      have htail : Visits p body shape [] 1 (advanceResult p e words) (advanceResult p e words) :=
        .done _ hfalse
      refine ⟨(nb + na) + 1 + 1, advanceResult p e words, ?_, hni, hfalse,
        advanceResult_scratch p e words, ?_⟩
      · simpa using Visits.step hf hshape hc hbody he hstep htail
      · simp only [ zero_add, one_mul]
        omega
    · have hbefore : CounterPrograms.value words.flatten + 1 < 2 ^ words.flatten.length := by
        omega
      obtain ⟨hcarry, hvalue⟩ := advance_before_last words hbefore
      have htrue : (advanceResult p e words).regs (p.register 2) = true := by
        simp only [advanceResult_flag, hcarry, Bool.not_false]
      have hrem : CounterPrograms.value (bumpWords words).2.flatten + fuel =
          2 ^ (bumpWords words).2.flatten.length := by
        rw [bumpWords_flatten_length, hvalue]
        omega
      obtain ⟨nt, f, ht, hfi, hff, hfs, hbound⟩ := ih (bumpWords words).2
        (advanceResult p e words) ((bumpWords_lengths words).trans hshape) hni
        (advanceResult_counter p e words) (advanceResult_scratch p e words) htrue hrem
      rw [bumpWords_encoded_length] at hbound
      refine ⟨(nb + na) + nt + 1, f, ?_, hfi, hff, hfs, ?_⟩
      · simpa only [List.range'_succ, hvalue] using Visits.step hf hshape hc hbody he hstep ht
      · rw [Nat.succ_mul]
        omega

/-- From zero payloads, the actual callback log is exactly all ranks below
2^B. It includes the callback and overflow increment at the final rank. -/
theorem enumerate_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget)
    (words : List (List Bool)) (d : Data R S)
    (hshape : words.map List.length = shape) (hi : I d)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = [])
    (hz : CounterPrograms.value words.flatten = 0) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) (1 + n) d e ∧
      Visits p body shape (List.range' 0 (2 ^ words.flatten.length)) n (startResult p d) e ∧
      I e ∧ e.regs (p.register 2) = false ∧ e.stacks p.scratch = [] ∧
      1 + n ≤ 2 ^ words.flatten.length *
        (budget + 7 * (Encoding.encodeList id words).length + 5) + 2 := by
  have hstart : StructuredCalls.Eval (startCmd p) 1 d (startResult p d) :=
    .base (.atom _ _)
  have hsi : I (startResult p d) := stable 0 d (startResult p d)
    (fun _ _ _ => rfl) hi
  obtain ⟨n, e, hv, hei, hef, hes, hn⟩ := loop_exists p body shape I budget stable spec
    (2 ^ words.flatten.length) words (startResult p d) hshape hsi
    (by simpa using hc) (by simpa using hs) (startResult_flag p d) (by rw [hz]; omega)
  exact ⟨n, e, .seq hstart hv.eval, by simpa only [hz] using hv,
    hei, hef, hes, by omega⟩

/-- Invariant-aware witness folding, for callbacks that need a fixed input
formula or a previously saved valid witness in their correctness statement. -/
theorem Visits.stack_fold_of_invariant {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) (j : Fin S)
    (hc : j ≠ p.counter) (hs : j ≠ p.scratch)
    (update : List Bool → ℕ → List Bool) (P : Data R S → Prop) (hP : P d)
    (hb : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → StructuredCalls.Eval body nb a b → P a →
      P b ∧ b.stacks j = update (a.stacks j) (CounterPrograms.value words.flatten))
    (hn : ∀ words a, P a → P (advanceResult p a words)) :
    P e ∧ e.stacks j = ranks.foldl update (d.stacks j) := by
  induction h with
  | done d hf => exact ⟨hP, rfl⟩
  | @step words d a e nb na nt ranks hf hw hd hbody ha hadv tail ih =>
    obtain ⟨hPa, hstack⟩ := hb words d a nb hw hd hbody hP
    obtain ⟨hPe, hfold⟩ := ih (hn words a hPa)
    refine ⟨hPe, ?_⟩
    rw [hfold, ← advanceResult_outside p a words j hc hs, hstack]
    rfl

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

/-- A local increment has polynomial workspace independently of how many
other increments have preceded it. Every caller stack is included. -/
theorem advance_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (words : List (List Bool)) (d : StructuredCalls.State R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words)
    (hs : d.stacks p.scratch = []) (boundaryBound : ℕ)
    (hb : ∀ i, (d.stacks i).length ≤ boundaryBound) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 4 ∧
      Eval (advanceCmd p) n d (advanceResult p d words) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (compiled (advanceCmd p) p.counter p.counter) prefixSteps
          (d.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          S * boundaryBound + 7 * (Encoding.encodeList id words).length + 4 := by
  obtain ⟨n, hn, he⟩ := advance_eval p words d hc hs
  refine ⟨n, hn, he, ?_⟩
  intro prefixSteps intermediate hle htrace i
  have hb' : dataBits
      (d.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) ≤
      S * boundaryBound := StreamResources.dataBits_le_mul _ hb
  have hp := StructuredSpace.local_stack_bound
    (compiled (advanceCmd p) p.counter p.counter)
    (steps := 7 * (Encoding.encodeList id words).length + 4)
    hb' prefixSteps intermediate (hle.trans hn) htrace i
  simpa only [Nat.add_assoc] using hp

/-- Every actual callback and controller prefix has one common storage bound.
The number of visits does not appear in the bound. -/
theorem visits_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) (shape : List ℕ)
    (I J : StructuredCalls.State R S → Prop) (boundaryBound callbackBound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hmiddle : ∀ a, J a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      a.regs (p.register 2) = true → J b ∧ b.stacks p.scratch = [] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body p.counter p.counter) prefixSteps
          (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (hnext : ∀ words a, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → J a →
      I (advanceResult p a words))
    {ranks : List ℕ} {steps : ℕ} {a b : StructuredCalls.State R S}
    (hvis : Visits p body shape ranks steps a b) (hI : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (loopCmd p body) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max callbackBound (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4) := by
  let bound := max callbackBound
    (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4)
  have hboundary : boundaryBound ≤ bound := by
    have hS : 1 ≤ S := by have := p.counter.isLt; omega
    have hmul : boundaryBound ≤ S * boundaryBound := by
      simpa using Nat.mul_le_mul_right boundaryBound hS
    exact hmul.trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _)))
  induction hvis with
  | done a hf =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf
        (fun i => (hinitial a hI i).trans hboundary)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
      obtain ⟨hmid, hscratch, hbody⟩ := hcallback words a middle nb hw hc hb hI hf
      have hafter := hnext words middle hw he hmid
      obtain ⟨n, _, hn, hlocal⟩ := advance_stack_bound p words middle he hscratch
        boundaryBound (hmiddle middle hmid)
      have htime : na = n := StreamResources.eval_steps_eq p.counter p.counter ha hn
      have hcontrol : ∀ prefixSteps intermediate, prefixSteps ≤ na →
          Trace (compiled (advanceCmd p) p.counter p.counter) prefixSteps
            (middle.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        rw [htime] at hle
        have h := hlocal prefixSteps intermediate hle htrace i
        rw [encoded_shape_length hw] at h
        exact h.trans (Nat.le_max_right _ _)
      have hcallbackBound : ∀ prefixSteps intermediate, prefixSteps ≤ nb →
          Trace (compiled body p.counter p.counter) prefixSteps
            (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        exact (hbody prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hcallbackBound hcontrol
        (compiled (.seq body (advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (advanceCmd p))) (exitAddress (.seq body (advanceCmd p)))
        (compiled_site _ p.counter p.counter)
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter)
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The iterator initialization and final halt preserve the loop's common
bound, so the theorem covers every prefix of the complete compiled program. -/
theorem enumerate_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) {shape ranks : List ℕ} {steps bound : ℕ}
    {a b : StructuredCalls.State R S}
    (hvis : Visits p body shape ranks steps (startResult p a) b)
    (hloop : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loopCmd p body) p.counter p.counter) prefixSteps
        ((startResult p a).withPC
          (some (compiled (loopCmd p body) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 + steps + 1 →
      Trace (program p body) prefixSteps
        (a.withPC (some (program p body).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  have hstart : Eval (startCmd p) 1 a (startResult p a) := .base (.atom _ _)
  have hinit : ∀ i, (a.stacks i).length ≤ bound :=
    hloop 0 _ (Nat.zero_le _) (.refl _)
  have hprefix : ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace (compiled (startCmd p) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (startCmd p) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have ht : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
    rcases ht with rfl | rfl
    · cases htrace
      exact hinit i
    · have heq := trace_same_length_unique htrace (compiled_trace hstart p.counter p.counter)
      rw [heq]
      exact hinit i
  have hseq := StructuredSpace.sequence_stack_bound hstart hvis.eval p.counter p.counter
    hprefix hloop (program p body) (siteAddress (enumerate p body))
    (exitAddress (enumerate p body)) (compiled_site _ p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq hstart hvis.eval)
    p.counter p.counter hseq

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem rejectionFrame_stable {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (base : State R S) :
    CounterForPrograms.FrameStable p (fun _ => RejectionFrame p latch base) := by
  intro _ a b hab ha
  refine ⟨?_, ?_⟩
  · intro i hi hj hk
    exact (hab i hi hj).symm.trans (ha.1 i hi hj hk)
  · obtain ⟨bit, hbit⟩ := ha.2
    exact ⟨bit, (hab latch hc hs).symm.trans hbit⟩

theorem rejectionFrame_update {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (base a out : State R S) (bit : Bool)
    (ha : RejectionFrame p latch base a)
    (hout : out.stacks = Function.update a.stacks latch [bit]) :
    RejectionFrame p latch base out := by
  refine ⟨?_, bit, ?_⟩
  · intro i hi hj hk
    rw [hout, Function.update_of_ne hk]
    exact ha.1 i hi hj hk
  · rw [hout, Function.update_self]

theorem RejectionBody.bodySpec {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {latch : Fin S} {body : Cmd R S} {dimension budget : ℕ}
    {base : State R S} {reject : ℕ → Bool}
    (h : RejectionBody p latch body dimension budget base reject)
    (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch) :
    ExecCNFTupleEnumeration.BodySpec p body (List.replicate dimension 2)
      (RejectionFrame p latch base) budget := by
  intro words a hw ha hac has
  obtain ⟨n, out, hn, he, ho⟩ := h.run words a hw ha hac has
  refine ⟨n, out, hn, he, ?_, ?_, rejectionFrame_update p latch base a out _ ha ho⟩
  · rw [ho, Function.update_of_ne (Ne.symm hc)]
    exact hac
  · rw [ho, Function.update_of_ne (Ne.symm hs)]
    exact has

theorem RejectionBody.actual {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {latch : Fin S} {body : Cmd R S} {dimension budget : ℕ}
    {base : State R S} {reject : ℕ → Bool}
    (h : RejectionBody p latch body dimension budget base reject)
    (words : List (List Bool)) (a out : State R S) (n : ℕ)
    (hw : words.map List.length = List.replicate dimension 2)
    (ha : RejectionFrame p latch base a)
    (hc : a.stacks p.counter = Encoding.encodeList id words)
    (hs : a.stacks p.scratch = []) (he : Eval body n a out) :
    n ≤ budget ∧ out.stacks = Function.update a.stacks latch
      [(a.stacks latch).headD false || reject (CounterPrograms.value words.flatten)] := by
  obtain ⟨m, b, hm, hb, hout⟩ := h.run words a hw ha hc hs
  have hnm := StreamResources.eval_steps_eq p.counter latch he hb
  have hob := Eval.final_unique p.counter he hb
  subst m
  subst b
  exact ⟨hm, hout⟩

private theorem rejection_fold (ranks : List ℕ) (reject : ℕ → Bool) (b : Bool) :
    ranks.foldl (fun word rank => [word.headD false || reject rank]) [b] =
      [b || ranks.any reject] := by
  induction ranks generalizing b with
  | nil => simp
  | cons rank ranks ih =>
      change ranks.foldl (fun word rank => [word.headD false || reject rank])
        [b || reject rank] = [b || (reject rank || ranks.any reject)]
      rw [ih, Bool.or_assoc]

/-- Full actual stream correctness and cost, including every padded candidate,
all losing checks, the terminal increment, initialization, and halt. -/
theorem rejection_scan_runs {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (a : State R S) (b : Bool)
    (hbody : RejectionBody p latch body dimension budget a reject)
    (hcounter : a.stacks p.counter =
      Encoding.encodeList id (List.replicate dimension [false, false]))
    (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b]) :
    ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program p body) n
        (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
      RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
      out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] := by
  let I := RejectionFrame p latch a
  have stable := rejectionFrame_stable p latch hc hs a
  have spec := hbody.bodySpec hc hs
  have hi : I a := ⟨fun _ _ _ _ => rfl, b, hlatch⟩
  obtain ⟨n, out, he, hv, ho, _, hscratchout, hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body (List.replicate dimension 2) I budget
      stable spec (List.replicate dimension [false, false]) a (by simp) hi
      hcounter hscratch (ExecCNFTupleEnumeration.zero_tuple_value dimension 2)
  have hp : 2 ^ (List.replicate dimension [false, false]).flatten.length = 4 ^ dimension := by
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul]
    change 2 ^ (dimension * 2) = 4 ^ dimension
    rw [Nat.mul_comm dimension 2, pow_mul]
    norm_num
  have hlen : (Encoding.encodeList id (List.replicate dimension [false, false])).length =
      6 * dimension + 1 := by
    rw [Enumerators.encoded_shape_length (by simp :
      (List.replicate dimension [false, false]).map List.length = List.replicate dimension 2)]
    simp
    omega
  have hstart : I (ExecCNFTupleEnumeration.startResult p a) :=
    stable 0 a _ (fun _ _ _ => rfl) hi
  obtain ⟨_, hfold⟩ := hv.stack_fold_of_invariant latch hc hs
    (fun word rank => [word.headD false || reject rank])
    (fun state => I state ∧ state.stacks p.scratch = []) ⟨hstart, hscratch⟩
    (by
      intro words start finish steps hw hcounter' hrun hI
      have hactual := hbody.actual words start finish steps hw hI.1 hcounter' hI.2 hrun
      have hout := hactual.2
      refine ⟨⟨rejectionFrame_update p latch a start finish _ hI.1 hout, ?_⟩, ?_⟩
      · rw [hout, Function.update_of_ne (Ne.symm hs)]
        exact hI.2
      · rw [hout, Function.update_self])
    (by
      intro words state hI
      exact ⟨stable 0 state _ (ExecCNFTupleEnumeration.advanceResult_outside p state words) hI.1,
        ExecCNFTupleEnumeration.advanceResult_scratch p state words⟩)
  refine ⟨1 + n + 1, out, ?_, compiled_halt_trace he p.counter p.counter,
    ho, hscratchout, ?_⟩
  · rw [hp, hlen] at hn
    nlinarith
  · rw [ExecCNFTupleEnumeration.startResult_stacks, hlatch, rejection_fold, hp] at hfold
    exact hfold

/-- The complete stream has a uniform prefix bound independent of its number
of iterations. Each body invocation uses only its polynomial local budget. -/
theorem rejection_visits_space {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (base : State R S) (hbody : RejectionBody p latch body dimension budget base reject)
    (B : ℕ) (hB : 1 ≤ B) {a out : State R S} {ranks : List ℕ} {steps : ℕ}
    (hvis : ExecCNFTupleEnumeration.Visits p body (List.replicate dimension 2) ranks steps a out)
    (ha : RejectionFrame p latch base a) (hab : ∀ i, (a.stacks i).length ≤ B)
    (has : a.stacks p.scratch = []) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (ExecCNFTupleEnumeration.loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (ExecCNFTupleEnumeration.loopCmd p body)
          p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4) := by
  let I : State R S → Prop := fun a => RejectionFrame p latch base a ∧
    (∀ i, (a.stacks i).length ≤ B) ∧ a.stacks p.scratch = []
  have hresult := Enumerators.visits_stack_bound p body (List.replicate dimension 2)
    I I B (B + budget) (fun _ h => h.2.1) (fun _ h => h.2.1)
    (by
      intro words start finish n hw hcounter he hI _
      obtain ⟨hn, hout⟩ := hbody.actual words start finish n hw hI.1 hcounter hI.2.2 he
      have hsfinish : finish.stacks p.scratch = [] := by
        rw [hout, Function.update_of_ne (Ne.symm hs)]
        exact hI.2.2
      refine ⟨⟨rejectionFrame_update p latch base start finish _ hI.1 hout, ?_, hsfinish⟩,
        hsfinish, ?_⟩
      · intro i
        by_cases hi : i = latch
        · subst i
          simpa [hout] using hB
        · rw [hout, Function.update_of_ne hi]
          exact hI.2.1 i
      · intro prefixSteps intermediate hle ht i
        have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
        change (intermediate.stacks i).length ≤ (start.stacks i).length + prefixSteps at hg
        have hi := hI.2.1 i
        omega)
    (by
      intro words state hw hcounter hI
      refine ⟨rejectionFrame_stable p latch hc hs base 0 state _
        (ExecCNFTupleEnumeration.advanceResult_outside p state words) hI.1, ?_,
        ExecCNFTupleEnumeration.advanceResult_scratch p state words⟩
      intro i
      by_cases hi : i = p.counter
      · subst i
        rw [ExecCNFTupleEnumeration.advanceResult_counter,
          ExecCNFTupleEnumeration.bumpWords_encoded_length, ← hcounter]
        exact hI.2.1 p.counter
      · by_cases hj : i = p.scratch
        · subst i
          simp
        · rw [← ExecCNFTupleEnumeration.advanceResult_outside p state words i hi hj]
          exact hI.2.1 i)
    hvis ⟨ha, hab, has⟩
  have hsize : 2 * (List.replicate dimension 2).sum +
      2 * (List.replicate dimension 2).length + 1 = 6 * dimension + 1 := by
    simp
    omega
  simpa only [hsize] using hresult

/-- Time and space hold on the same complete source trace. The uniform storage
bound contains no exponential iteration count. -/
theorem rejection_scan_runs_space_oai {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (a : State R S) (b : Bool)
    (hbody : RejectionBody p latch body dimension budget a reject)
    (hcounter : a.stacks p.counter =
      Encoding.encodeList id (List.replicate dimension [false, false]))
    (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program p body) n
        (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
      RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
      out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program p body) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4)) := by
  obtain ⟨n, out, hn, ht, hf, hsout, hlout⟩ := rejection_scan_runs p latch hc hs body
    dimension budget reject a b hbody hcounter hscratch hlatch
  have hi : RejectionFrame p latch a a := ⟨fun _ _ _ _ => rfl, b, hlatch⟩
  have stable := rejectionFrame_stable p latch hc hs a
  obtain ⟨m, other, he, hv, _, _, _, _⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body (List.replicate dimension 2)
      (RejectionFrame p latch a) budget stable (hbody.bodySpec hc hs)
      (List.replicate dimension [false, false]) a (by simp) hi hcounter hscratch
      (ExecCNFTupleEnumeration.zero_tuple_value dimension 2)
  have hloop := rejection_visits_space p latch hc hs body dimension budget reject a hbody B hB hv
    (stable 0 a _ (fun _ _ _ => rfl) hi) ha hscratch
  have hspace := Enumerators.enumerate_stack_bound p body hv hloop
  have hnm := StreamResources.halted_trace_steps_eq ht
    (compiled_halt_trace he p.counter p.counter) (by rfl) (by rfl)
  refine ⟨n, out, hn, ht, hf, hsout, hlout, ?_⟩
  intro prefixSteps intermediate hle hprefix i
  apply hspace prefixSteps intermediate _ hprefix i
  rwa [← hnm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space_oai
