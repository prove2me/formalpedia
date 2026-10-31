-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:28:57.650993+00:00
-- url     : https://prove2.me/submissions/84127a82-e46b-4830-9dd0-187fe6c6558d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

/-- The final borrow is a comparison result produced by the measured program,
not by a natural-number comparison instruction. -/
theorem subtract_comparison (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hborrow : regs 0 = false) (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractProgram (12 * xs.length + 3)
        (subtractCfg (some 0) regs xs ys [])
        (subtractCfg none finalRegs [] [] (subCarry false xs ys).1.reverse) ∧
      (finalRegs 0 = true ↔
        SubexponentialSAT.BinaryArithmetic.toNat xs < SubexponentialSAT.BinaryArithmetic.toNat ys) := by
  obtain ⟨finalRegs, hrun, hfinal⟩ := subtract_correct regs xs ys [] hlen
  refine ⟨finalRegs, ?_, ?_⟩
  · simpa [hborrow] using hrun
  · rw [hfinal, hborrow]
    exact subCarry_borrow_iff xs ys hlen

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
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


/-- A completed actual traversal resets every payload bit while retaining all
record widths. This lets successive scans reuse the same counter frame. -/
theorem visits_reset_counter {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {body : StructuredCalls.Cmd R S} {shape ranks : List ℕ} {steps : ℕ}
    {a b : StructuredCalls.State R S} (h : Visits p body shape ranks steps a b)
    (hstart : a.regs (p.register 2) = true) :
    b.stacks p.counter = Encoding.encodeList id
      (shape.map (fun width => List.replicate width false)) := by
  have hflat : (shape.map (fun width => List.replicate width false)).flatten =
      List.replicate shape.sum false := by
    clear h hstart
    induction shape with
    | nil => rfl
    | cons width shape ih => simp [ih]
  have haux : (a.regs (p.register 2) = false → a.stacks p.counter =
      Encoding.encodeList id (shape.map (fun width => List.replicate width false))) →
      b.stacks p.counter = Encoding.encodeList id
        (shape.map (fun width => List.replicate width false)) := by
    clear hstart
    induction h with
    | done a hf => exact fun hz => hz hf
    | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
        intro _
        apply ih
        intro hfalse
        have hcarry : (ExecCNFTupleOdometer.bumpWords words).1 = true := by
          simpa only [advanceResult_flag, Bool.not_eq_false_eq_eq_true] using hfalse
        have hv := ExecCNFTupleOdometer.bumpWords_value words
        simp only [hcarry, ite_true, if_true] at hv
        have hlt := ExecCNFTupleOdometer.value_lt_power_length words.flatten
        have hz : CounterPrograms.value
            (ExecCNFTupleOdometer.bumpWords words).2.flatten = 0 := by omega
        rw [advanceResult_counter]
        apply congrArg (Encoding.encodeList id)
        apply tuple_eq_of_shape_value
        · simpa only [ExecCNFTupleOdometer.bumpWords_lengths, List.map_map,
            Function.comp_def, List.length_replicate, List.map_id'] using hw
        · simpa only [hflat, value_replicate_false] using hz
  apply haux
  intro hfalse
  simp only [hstart, Bool.true_eq_false] at hfalse

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem reset_eval (d : Data) : Eval (atom (.set 0 false)) 1 d (reset d) := by
  exact Eval.base (StructuredProgram.Eval.atom (.set 0 false) d)

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

private theorem state_ext {a b : Data}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embed_input (d : Data) (h6 : d.stacks 6 = []) :
    embedState id compareStacks d
      ⟨d.regs, ModularPrograms.operandStacks (d.stacks 4) (d.stacks 5) []⟩ = d := by
  apply state_ext
  · funext j
    exact embedState_register _ _ _ _ Function.injective_id j
  · funext j
    by_cases h : ∃ i, compareStacks i = j
    · obtain ⟨i, rfl⟩ := h
      rw [embedState_stack _ _ _ _ compareStacks_injective]
      fin_cases i <;> simp [compareStacks, ModularPrograms.operandStacks, h6]
    · exact embedState_stack_frame _ _ _ _ j h

/-- Destructive binary comparison; only scratch stacks 4, 5, 6 change. -/
theorem compare_eval (d : Data) (h0 : d.regs 0 = false)
    (h6 : d.stacks 6 = []) (hlen : (d.stacks 4).length = (d.stacks 5).length) :
    ∃ e : Data,
      Eval (.call comparator) (12 * (d.stacks 4).length + 3) d e ∧
      (e.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 4) <
        BinaryArithmetic.toNat (d.stacks 5)) ∧
      e.stacks 4 = [] ∧ e.stacks 5 = [] ∧
      (e.stacks 6).length = (d.stacks 4).length ∧
      (∀ j : Fin 9, j ≠ 4 → j ≠ 5 → j ≠ 6 → e.stacks j = d.stacks j) := by
  obtain ⟨regs, ht, hb⟩ := ModularPrograms.subtract_comparison d.regs
    (d.stacks 4) (d.stacks 5) h0 hlen
  let out : State 8 3 := ⟨regs, ModularPrograms.operandStacks [] []
    (ModularArithmetic.subCarry false (d.stacks 4) (d.stacks 5)).1.reverse⟩
  let e := embedState id compareStacks d out
  change Trace ModularPrograms.subtractProgram _
    ((⟨d.regs, ModularPrograms.operandStacks (d.stacks 4) (d.stacks 5) []⟩ :
      State 8 3).withPC (some ModularPrograms.subtractProgram.entry))
    (out.withPC none) at ht
  have he := eval_call_lifted ModularPrograms.subtractProgram id compareStacks d
    Function.injective_id compareStacks_injective ht
  rw [embed_input d h6] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_⟩
  · change (embedState id compareStacks d out).regs (id 0) = true ↔ _
    rw [embedState_register _ _ _ _ Function.injective_id]
    exact hb
  · exact embedState_stack _ _ _ _ compareStacks_injective 0
  · exact embedState_stack _ _ _ _ compareStacks_injective 1
  · change ((embedState id compareStacks d out).stacks (compareStacks 2)).length = _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [out] using ModularArithmetic.subCarry_length false
      (d.stacks 4) (d.stacks 5) hlen
  · intro j h4 h5 h6
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [compareStacks]

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

/-- One strict-improvement update. The bound depends on bit lengths, never on
the numeric score. The queue and the first incumbent on equal scores survive. -/
theorem update_eval (B C : ℕ) (next best : Entry) (queue : List Bool)
    (regs : Fin 8 → Bool) (hn : next.score.length = B)
    (hb : best.score.length = B) (hcn : next.payload.length ≤ C)
    (hcb : best.payload.length ≤ C) :
    ∃ n ≤ 100 * (B + C + 1), ∃ regs',
      Eval update n (data regs next best queue)
        (data regs' empty (pick best next) queue) := by
  let d := data regs next best queue
  let a := afterCopy d 1 4
  let b := afterCopy a 3 5
  let c := reset b
  have hcopy1 := copy_eval d 1 4 (by decide) (by decide) (by decide) (by rfl)
  have hcopy2 := copy_eval a 3 5 (by decide) (by decide) (by decide) (by rfl)
  have hc4 : c.stacks 4 = next.score := by simp [c, b, a, d, reset, afterCopy, copyStacks, data, store]
  have hc5 : c.stacks 5 = best.score := by simp [c, b, a, d, reset, afterCopy, copyStacks, data, store]
  obtain ⟨e, he, hlt, he4, he5, he6, hef⟩ := compare_eval c (by simp [c, reset])
    (by rfl) (by rw [hc4, hc5, hn, hb])
  rw [hc4, hc5] at hlt
  rw [hc4, hn] at he6
  have he0 : e.stacks 0 = next.payload := by
    rw [hef 0 (by decide) (by decide) (by decide)]; rfl
  have he1 : e.stacks 1 = next.score := by
    rw [hef 1 (by decide) (by decide) (by decide)]; rfl
  have he2 : e.stacks 2 = best.payload := by
    rw [hef 2 (by decide) (by decide) (by decide)]; rfl
  have he3 : e.stacks 3 = best.score := by
    rw [hef 3 (by decide) (by decide) (by decide)]; rfl
  have he7 : e.stacks 7 = [] := by
    rw [hef 7 (by decide) (by decide) (by decide)]; rfl
  have he8 : e.stacks 8 = queue := by
    rw [hef 8 (by decide) (by decide) (by decide)]; rfl
  let k := if value next < value best then afterReplace e else e
  have hbranch : ∃ m ≤ 9 * C + 9 * B + 17,
      Eval (.ite 0 replace (.base .skip)) m e k := by
    by_cases h : value next < value best
    · refine ⟨2 * (e.stacks 2).length + 7 * (e.stacks 0).length +
        2 * (e.stacks 3).length + 7 * (e.stacks 1).length + 16 + 1, ?_, ?_⟩
      · rw [he2, he0, he3, he1, hn, hb]; omega
      · simpa [k, h] using Eval.ite_true (hlt.mpr h) (replace_eval e he7)
    · refine ⟨1, by omega, ?_⟩
      have hf : e.regs 0 = false := by
        cases hv : e.regs 0 <;> simp_all [value]
      simpa [k, h] using Eval.ite_false hf (Eval.base (.skip e))
  obtain ⟨m, hm, hbranch⟩ := hbranch
  have hk0 : k.stacks 0 = next.payload := by
    dsimp only [k]
    split_ifs <;> simp [afterReplace, afterCopy, afterClear, copyStacks, clearStacks, he0]
  have hk1 : k.stacks 1 = next.score := by
    dsimp only [k]
    split_ifs <;> simp [afterReplace, afterCopy, afterClear, copyStacks, clearStacks, he1]
  have hk6 : (k.stacks 6).length = B := by
    dsimp only [k]
    split_ifs <;> simpa [afterReplace, afterCopy, afterClear, copyStacks, clearStacks] using he6
  have hfinal : afterCleanup k =
      data (afterCleanup k).regs empty (pick best next) queue := by
    apply state_ext
    · rfl
    · funext j
      by_cases h : value next < value best <;> fin_cases j <;>
        simp [afterCleanup, k, pick, h, afterReplace, afterClear, afterCopy,
          clearStacks, copyStacks, data, store, empty, he0, he1, he2, he3, he4, he5, he7, he8]
  let total := (7 * (d.stacks 1).length + 5) +
    ((7 * (a.stacks 3).length + 5) +
      (1 + ((12 * (c.stacks 4).length + 3) +
        (m + (2 * (k.stacks 0).length + 2 * (k.stacks 1).length +
          2 * (k.stacks 6).length + 9)))))
  refine ⟨total, ?_, (afterCleanup k).regs, ?_⟩
  · simp only [total, hk0, hk1, hk6, hc4]
    have hd1 : d.stacks 1 = next.score := rfl
    have ha3 : a.stacks 3 = best.score := rfl
    rw [hd1, ha3, hn, hb]
    omega
  · rw [← hfinal]
    exact Eval.seq hcopy1 (Eval.seq hcopy2 (Eval.seq (reset_eval b)
      (Eval.seq he (Eval.seq hbranch (cleanup_eval k)))))

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

theorem best_le_seed (score : R → ℕ) (seed : R) (rs : List R) :
    score (best score seed rs) ≤ score seed := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    split_ifs with h
    · exact (ih r).trans (Nat.le_of_lt h)
    · exact ih seed

theorem best_le_member (score : R → ℕ) (seed : R) (rs : List R)
    (r : R) (hr : r ∈ rs) :
    score (best score seed rs) ≤ score r := by
  induction rs generalizing seed with
  | nil => simp at hr
  | cons a rs ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst a
      simp only [best]
      split_ifs with hs
      · exact best_le_seed score r rs
      · exact (best_le_seed score seed rs).trans (Nat.le_of_not_gt hs)
    · simp only [best]
      exact ih _ h

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgminScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A measured binary argmin scan with a paid loader

`LoaderSpec` is a refinement obligation on a fixed, executable command. It
requires an actual `StructuredCalls.Eval` for every callback, including the
final empty callback; it is not an oracle or an instruction for evaluating a
mathematical score. A caller may satisfy it by parsing prepared records or by
enumerating candidates and executing a score program. The incumbent score is
cached. Its first evaluation and the preparation of the initial incumbent are
outside this scan and must be charged by the caller.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem pick_fits {B C : ℕ} {best next : Entry}
    (hb : Fits B C best) (hn : Fits B C next) : Fits B C (pick best next) := by
  unfold pick
  split_ifs <;> assumption

end SubexponentialSAT.SqrtLog.BinaryArgmin

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

theorem advance_readEntry {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (payload score : Fin s) (a : State r s) (words : List (List Bool))
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch) :
    readEntry payload score (ExecCNFTupleEnumeration.advanceResult p a words) =
      readEntry payload score a := by
  apply congrArg₂ BinaryArgmin.Entry.mk
  · exact (ExecCNFTupleEnumeration.advanceResult_outside p a words payload hpc hps).symm
  · exact (ExecCNFTupleEnumeration.advanceResult_outside p a words score hsc hss).symm

/-- Refinement of a genuine iterator trace to the cached strict argmin.
`ranks` is proof evidence of visits, never a machine stack or runtime list.
The body premise concerns its actual measured execution and must be discharged
by candidate loading, normalization, exact scoring, and `updateProgram`. -/
theorem visits_best {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (body : Cmd r s) (shape : List ℕ) (payload score : Fin s)
    (entry : ℕ → BinaryArgmin.Entry) (I : State r s → Prop)
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch)
    (hbody : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      readEntry payload score b = BinaryArgmin.pick (readEntry payload score a)
        (entry (CounterPrograms.value words.flatten)) ∧
      I (ExecCNFTupleEnumeration.advanceResult p b words))
    {ranks : List ℕ} {steps : ℕ} {a b : State r s}
    (hvis : ExecCNFTupleEnumeration.Visits p body shape ranks steps a b) (hI : I a) :
    readEntry payload score b = HashSelect.best BinaryArgmin.value
      (readEntry payload score a) (ranks.map entry) := by
  induction hvis with
  | done a hf => rfl
  | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
    obtain ⟨hselected, hnext⟩ := hbody words a middle nb hw hc hb hI
    rw [ih hnext, advance_readEntry p payload score middle words hpc hps hsc hss,
      hselected]
    rfl

/-- Every losing callback contributes a comparison constraint on the actual
returned binary score, not only on a semantic annotation. -/
theorem visits_minimum {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (body : Cmd r s) (shape : List ℕ) (payload score : Fin s)
    (entry : ℕ → BinaryArgmin.Entry) (I : State r s → Prop)
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch)
    (hbody : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      readEntry payload score b = BinaryArgmin.pick (readEntry payload score a)
        (entry (CounterPrograms.value words.flatten)) ∧
      I (ExecCNFTupleEnumeration.advanceResult p b words))
    {ranks : List ℕ} {steps : ℕ} {a b : State r s}
    (hvis : ExecCNFTupleEnumeration.Visits p body shape ranks steps a b) (hI : I a) :
    readEntry payload score b ∈ readEntry payload score a :: ranks.map entry ∧
      ∀ j ∈ ranks, BinaryArgmin.value (readEntry payload score b) ≤
        BinaryArgmin.value (entry j) := by
  rw [visits_best p body shape payload score entry I hpc hps hsc hss hbody hvis hI]
  refine ⟨HashSelect.best_mem _ _ _, ?_⟩
  intro j hj
  exact HashSelect.best_le_member _ _ _ _ (List.mem_map.mpr ⟨j, hj, rfl⟩)


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

/-- Actual score comparison, with an exact whole-bank frame statement. -/
theorem update_eval (a : State 40 896) (B C : ℕ) (hc : CoreClean a)
    (hn : BinaryArgmin.Fits B C (readEntry 768 769 a))
    (hb : BinaryArgmin.Fits B C (readEntry 770 771 a)) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ b,
      Eval (HashSelectProgram.update core) n a b ∧
      b.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a) (readEntry 768 769 a)) := by
  obtain ⟨n, hn', rf, he⟩ := BinaryArgmin.update_eval B C
    (readEntry 768 769 a) (readEntry 770 771 a) []
    (fun i => a.regs (registers i)) hn.1 hb.1 hn.2 hb.2
  have ht := compiled_halt_trace he 8 2
  rw [← projected_core a hc] at ht
  refine ⟨n + 1, by omega, _,
    eval_call_from_state _ registers coreStacks a
      core.register_injective core.stack_injective ht, ?_⟩
  exact embed_core_stacks a hc rf _

/-- Once the actual preparation/query/padding trace is supplied, the cached
minimum step follows with every other stack preserved. -/
theorem body_eval_of_attempt (mass : Cmd 40 896) (a b : State 40 896)
    (na B C : ℕ) (next : BinaryArgmin.Entry)
    (ha : Eval (attempt mass) na a b)
    (hframe : b.stacks = Function.update (Function.update a.stacks 768 next.payload) 769 next.score)
    (hc : CoreClean a) (hn : BinaryArgmin.Fits B C next)
    (hb : BinaryArgmin.Fits B C (readEntry 770 771 a)) :
    ∃ n ≤ na + (100 * (B + C + 1) + 1), ∃ c,
      Eval (body mass) n a c ∧
      c.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a) next) := by
  have hc' : CoreClean b := by
    constructor <;> simp [hframe, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]
  have hn' : readEntry 768 769 b = next := by simp [readEntry, hframe]
  have hb' : readEntry 770 771 b = readEntry 770 771 a := by simp [readEntry, hframe]
  obtain ⟨n, hcost, c, he, hout⟩ := update_eval b B C hc'
    (by simpa only [hn'] using hn) (by simpa only [hb'] using hb)
  refine ⟨na + n, by omega, c, ha.seq he, ?_⟩
  rw [hout, hn', hb']
  funext i
  by_cases h0 : i = 768 <;> by_cases h1 : i = 769 <;>
    simp [stored, hframe, Function.update_apply, h0, h1]

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

theorem boundary_stable (base : State 40 896) (B C : ℕ) :
    CounterForPrograms.FrameStable counter (fun _ => Boundary base B C) := by
  intro q a b hframe ha
  constructor
  · intro i h0 h1 h2 h3
    rw [← hframe i h2 h3]
    exact ha.frame i h0 h1 h2 h3
  · have hp := hframe 770 (by decide) (by decide)
    have hs := hframe 771 (by decide) (by decide)
    simpa only [readEntry, ← hp, ← hs] using ha.fits

theorem boundary_core (base a : State 40 896) (B C : ℕ)
    (hb : CoreClean base) (ha : Boundary base B C a) : CoreClean a := by
  constructor
  · rw [ha.frame 772 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch772
  · rw [ha.frame 773 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch773
  · rw [ha.frame 774 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch774
  · rw [ha.frame 775 (by decide) (by decide) (by decide) (by decide)]
    exact hb.scratch775
  · rw [ha.frame 776 (by decide) (by decide) (by decide) (by decide)]
    exact hb.queue776

theorem boundary_stored (base a b : State 40 896) (B C : ℕ)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = [])
    (ha : Boundary base B C a) (winner : BinaryArgmin.Entry)
    (hw : BinaryArgmin.Fits B C winner) (hb : b.stacks = stored a winner) :
    Boundary base B C b := by
  constructor
  · intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hb, stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hb, stored, h1]
    simpa [hb, stored, h768, h769, h770, h771] using
      ha.frame i h770 h771 h778 h779
  · simpa [readEntry, hb, stored] using hw

private theorem shape_flatten_length {words : List (List Bool)} {C : ℕ}
    (hw : words.map List.length = [C]) : words.flatten.length = C := by
  have h := congrArg List.sum hw
  simpa [List.length_flatten] using h

/-- Every actual candidate, including losing candidates, pays the attempt and
native comparison costs. No candidate family is allocated in the machine. -/
theorem body_execution (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (words : List (List Bool)) (a : State 40 896)
    (hw : words.map List.length = [C]) (ha : Boundary base B C a)
    (hcounter : a.stacks 778 = Encoding.encodeList id words) (hscratch : a.stacks 779 = []) :
    ∃ n ≤ attemptCost + (100 * (B + C + 1) + 1), ∃ b,
      Eval (body mass) n a b ∧
      b.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a)
        (entry (CounterPrograms.value words.flatten))) := by
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  obtain ⟨n, hn, b, he, hb⟩ := hattempt words a hw ha hcounter hscratch
  obtain ⟨t, ht, c, hc, hs⟩ := body_eval_of_attempt mass a b n B C
    (entry (CounterPrograms.value words.flatten)) he hb
    (boundary_core base a B C hcore ha) (hfit _ hrank) ha.fits
  exact ⟨t, by omega, c, hc, hs⟩

/-- Instantiate the real finite iterator from the paid native attempt traces.
The only changing stored values are the incumbent and bounded odometer. -/
theorem body_spec (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ExecCNFTupleEnumeration.BodySpec counter (body mass) [C] (Boundary base B C)
      (attemptCost + (100 * (B + C + 1) + 1)) := by
  intro words a hw ha hc hs
  obtain ⟨n, hn, b, he, hb⟩ := body_execution mass base B C attemptCost entry hcore
    hfit hattempt words a hw ha hc hs
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  refine ⟨n, b, hn, he, ?_, ?_, ?_⟩
  · simpa [hb, stored, counter] using hc
  · simpa [hb, stored, counter] using hs
  · exact boundary_stored base a b B C h0 h1 ha _
      (BinaryArgmin.pick_fits ha.fits (hfit _ hrank)) hb

/-- Determinism identifies every actual update trace with the measured native
one, including its restored scratch and the next odometer boundary. -/
theorem body_refines (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (words : List (List Bool)) (a b : State 40 896) (n : ℕ)
    (hw : words.map List.length = [C]) (hc : a.stacks 778 = Encoding.encodeList id words)
    (he : Eval (body mass) n a b) (ha : Boundary base B C a) (hs : a.stacks 779 = []) :
    readEntry 770 771 b = BinaryArgmin.pick (readEntry 770 771 a)
      (entry (CounterPrograms.value words.flatten)) ∧
      Boundary base B C (ExecCNFTupleEnumeration.advanceResult counter b words) ∧
      (ExecCNFTupleEnumeration.advanceResult counter b words).stacks 779 = [] := by
  obtain ⟨t, _, c, ht, hout⟩ := body_execution mass base B C attemptCost entry hcore
    hfit hattempt words a hw ha hc hs
  have hbc : b = c := he.final_unique 778 ht
  subst c
  have hrank : CounterPrograms.value words.flatten < 2 ^ C := by
    simpa only [shape_flatten_length hw] using
      ExecCNFTupleOdometer.value_lt_power_length words.flatten
  have hb := boundary_stored base a b B C h0 h1 ha _
    (BinaryArgmin.pick_fits ha.fits (hfit _ hrank)) hout
  refine ⟨?_, boundary_stable base B C 0 b _
    (ExecCNFTupleEnumeration.advanceResult_outside counter b words) hb, ?_⟩
  · simp [readEntry, hout, stored]
  · exact ExecCNFTupleEnumeration.advanceResult_scratch counter b words

/-- The complete native scan returns an attained minimum, preserves every
fixed caller word, and resets the singleton counter for the next round. -/
theorem scan_minimum_oai (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ 2 ^ C * (attemptCost + (100 * (B + C + 1) + 1) + 7 * (2 * C + 3) + 5) + 2,
      ∃ b, Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) n base b ∧
        Boundary base B C b ∧ b.stacks 779 = [] ∧
        b.stacks 778 = Encoding.encodeList id [List.replicate C false] ∧
        (∃ j < 2 ^ C, readEntry 770 771 b = entry j) ∧
        (∀ j < 2 ^ C, BinaryArgmin.value (readEntry 770 771 b) ≤ BinaryArgmin.value (entry j)) ∧
        readEntry 770 771 b = HashSelect.best BinaryArgmin.value (entry 0)
          ((List.range' 0 (2 ^ C)).map entry) := by
  have hi : Boundary base B C base := by
    refine ⟨fun _ _ _ _ _ => rfl, ?_⟩
    rw [hseed]
    exact hfit 0 (pow_pos (by decide) _)
  have spec := body_spec mass base B C attemptCost entry h0 h1 hcore hfit hattempt
  obtain ⟨n, b, he, hv, hb, _, hscratch', hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct counter (body mass) [C] (Boundary base B C)
      (attemptCost + (100 * (B + C + 1) + 1)) (boundary_stable base B C) spec
      [List.replicate C false] base (by simp) hi hcounter hscratch
      (by simp)
  have hstart : Boundary base B C (ExecCNFTupleEnumeration.startResult counter base) :=
    boundary_stable base B C 0 base _ (fun _ _ _ => rfl) hi
  have hrefine : ∀ words a b nb, words.map List.length = [C] →
      a.stacks counter.counter = Encoding.encodeList id words → Eval (body mass) nb a b →
      (Boundary base B C a ∧ a.stacks 779 = []) →
      readEntry 770 771 b = BinaryArgmin.pick (readEntry 770 771 a)
        (entry (CounterPrograms.value words.flatten)) ∧
      (Boundary base B C (ExecCNFTupleEnumeration.advanceResult counter b words) ∧
        (ExecCNFTupleEnumeration.advanceResult counter b words).stacks 779 = []) := by
    intro words a b nb hw hc he ha
    exact body_refines mass base B C attemptCost entry h0 h1 hcore hfit hattempt
      words a b nb hw hc he ha.1 ha.2
  obtain ⟨hmem, hmin⟩ := visits_minimum counter (body mass) [C] 770 771 entry
    (fun a => Boundary base B C a ∧ a.stacks 779 = [])
    (by decide) (by decide) (by decide) (by decide) hrefine hv
    ⟨hstart, hscratch⟩
  have hbest := visits_best counter (body mass) [C] 770 771 entry
    (fun a => Boundary base B C a ∧ a.stacks 779 = [])
    (by decide) (by decide) (by decide) (by decide) hrefine hv
    ⟨hstart, hscratch⟩
  have hreset := Enumerators.visits_reset_counter hv
    (ExecCNFTupleEnumeration.startResult_flag counter base)
  have hflat : ([List.replicate C false] : List (List Bool)).flatten.length = C := by simp
  rw [hflat] at hn hmem hmin hbest
  change readEntry 770 771 b ∈ readEntry 770 771 base :: _ at hmem
  change readEntry 770 771 b = HashSelect.best BinaryArgmin.value
    (readEntry 770 771 base) _ at hbest
  rw [hseed] at hmem hbest
  refine ⟨1 + n, ?_, b, he, hb, hscratch', ?_, ?_, ?_, hbest⟩
  · simpa [Encoding.encodeList, Encoding.length_frame] using hn
  · change b.stacks counter.counter = Encoding.encodeList id [List.replicate C false]
    exact hreset
  · rcases List.mem_cons.mp hmem with hfirst | hrest
    · exact ⟨0, pow_pos (by decide) _, hfirst⟩
    · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hrest
      exact ⟨j, by simpa using hj, heq.symm⟩
  · intro j hj
    exact hmin j (by simpa using hj)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum_oai
