-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:39:52.730978+00:00
-- url     : https://prove2.me/submissions/c54c6149-f3f7-4f38-a7f8-7efd9573040e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S137
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

/-- Later candidates still pay the branch, but never overwrite the witness. -/
theorem firstSuccessStep_skip {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hf : a.regs found = true) :
    StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
      1 a a :=
  .ite_true hf (.base (.skip a))

theorem firstSuccessStep_reject {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (hf : a.regs found = false)
    (hc : StructuredCalls.Eval check n a b) (hno : b.regs accepted = false) :
    StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
      (n + 2) a b := by
  convert StructuredCalls.Eval.ite_false hf
    (StructuredCalls.Eval.seq hc (StructuredCalls.Eval.ite_false hno (.base (.skip b)))) using 1
  · rfl

/-- The successful case pays for copying the entire candidate into the saved
witness port. The temporary copy stack is empty again at return. -/
theorem firstSuccessStep_accept {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (hf : a.regs found = false)
    (hc : StructuredCalls.Eval check n a b) (hyes : b.regs accepted = true)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) (hs : b.stacks selected = []) :
    ∃ c : StructuredCalls.State R S,
      StructuredCalls.Eval (firstSuccessStep check found accepted value present current selected scratch)
        (n + 7 * (b.stacks current).length + 8) a c ∧
      c.regs found = true ∧ c.stacks selected = b.stacks current ∧
      (∀ i, i ≠ selected → c.stacks i = b.stacks i) := by
  let copied : StructuredCalls.State R S :=
    ⟨readRegs b.regs value present none, StackRoutines.copyStacks current selected b.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram current selected scratch value present))
      (7 * (b.stacks current).length + 5) b copied :=
    .call _ (ListRegisterProgram.copy_run current selected scratch value present
      hcs hct hts hvp b.regs b.stacks ht)
  let c := (StructuredProgram.Atom.set (s := S) found true).eval copied
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · have h : StructuredCalls.Eval
        (firstSuccessStep check found accepted value present current selected scratch)
        (n + ((7 * (b.stacks current).length + 5 + 1) + 1) + 1) a c :=
      .ite_false hf (.seq hc (.ite_true hyes
        (.seq (n := 7 * (b.stacks current).length + 5) (m := 1)
          hcopy (.base (.atom _ _)))))
    simpa [Nat.add_assoc] using h
  · simp [c, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg]
  · simp [c, copied, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg,
      StackRoutines.copyStacks, hs]
  · intro i hi
    simp [c, copied, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg,
      StackRoutines.copyStacks, hi]

theorem firstSuccess_saved {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hne : a.stacks selected ≠ []) :
    ∃ b, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) 2 a b ∧
      b.stacks = a.stacks := by
  let b := (StructuredProgram.Atom.peek selected value found).eval a
  have hb : b.regs found = true := by
    simp [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs,
      List.isSome_head?, hne]
  exact ⟨b, .seq (.base (.atom _ _))
    (firstSuccessStep_skip check found accepted value present current selected scratch b hb), rfl⟩

/-- A fresh selection invokes the real checker after the physical empty-stack
peek. This lemma exposes the success case to the outer iterator invariant. -/
theorem firstSuccess_fresh_accept {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hyes : b.regs accepted = true)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) (hs : b.stacks selected = []) :
    ∃ c : StructuredCalls.State R S,
      StructuredCalls.Eval (firstSuccess check found accepted value present current selected scratch)
        (n + 7 * (b.stacks current).length + 9) a c ∧
      c.stacks selected = b.stacks current ∧
      (∀ i, i ≠ selected → c.stacks i = b.stacks i) := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  obtain ⟨c, he, _, hselected, hframe⟩ := firstSuccessStep_accept check found accepted value present
    current selected scratch entry b hf hc hyes hcs hct hts hvp ht hs
  refine ⟨c, ?_, hselected, hframe⟩
  have h : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch)
      (1 + (n + 7 * (b.stacks current).length + 8)) a c := .seq (.base (.atom _ _)) he
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem firstSuccess_fresh_reject {R S n : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hno : b.regs accepted = false) :
    StructuredCalls.Eval (firstSuccess check found accepted value present current selected scratch)
      (n + 3) a b := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  have he := firstSuccessStep_reject check found accepted value present current selected scratch
    entry b hf hc hno
  have h : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch)
      (1 + (n + 2)) a b := .seq (.base (.atom _ _)) he
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

/-- Once a native callback has saved a witness, every subsequent callback
and odometer increment preserves those exact bytes. -/
theorem search_retains_selected {R S steps : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (hc : selected ≠ ports.counter)
    (hs : selected ≠ ports.scratch) {shape ranks : List ℕ}
    {a b : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      shape ranks steps a b) (hne : a.stacks selected ≠ []) :
    b.stacks selected = a.stacks selected := by
  induction visits with
  | done => rfl
  | @step words start middle finish nb na nt ranks hflag hshape hcounter hbody
      hpreserve hadvance tail ih =>
      obtain ⟨out, hout, hframe⟩ := firstSuccess_saved check found accepted value present
        ports.counter selected copyScratch start hne
      have heq := hbody.final_unique ports.counter hout
      have hmiddle : middle.stacks selected = start.stacks selected := by
        rw [heq, hframe]
      have hnext := ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs
      rw [ih (by rw [← hnext, hmiddle]; exact hne), ← hnext, hmiddle]

/-- A covered successful candidate forces a nonempty native result. This
uses the actual occurrence and its remaining execution, without choosing an
abstract matrix or materializing a family of candidates. -/
theorem search_reaches_success {R S steps : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (hc : selected ≠ ports.counter)
    (hs : selected ≠ ports.scratch) {shape ranks : List ℕ}
    {a b : StructuredCalls.State R S}
    (visits : ExecCNFTupleEnumeration.Visits ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      shape ranks steps a b) (I : StructuredCalls.State R S → Prop) (hi : I a)
    (hcallback : ∀ words start finish cost, words.map List.length = shape →
      start.stacks ports.counter = Encoding.encodeList id words →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        cost start finish → I start → I finish)
    (hnext : ∀ words start, I start → I (ExecCNFTupleEnumeration.advanceResult ports start words))
    (target : List (List Bool)) (htarget : target.map List.length = shape)
    (hmember : CounterPrograms.value target.flatten ∈ ranks)
    (hsuccess : ∀ start finish cost,
      start.stacks ports.counter = Encoding.encodeList id target →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        cost start finish → I start → finish.stacks selected ≠ []) :
    b.stacks selected ≠ [] := by
  induction visits with
  | done => simp at hmember
  | @step words start middle finish nb na nt ranks hflag hshape hcounter hbody
      hpreserve hadvance tail ih =>
      have hmiddle := hcallback words start middle nb hshape hcounter hbody hi
      rcases List.mem_cons.mp hmember with hhead | htail
      · have hwords : words = target := ExecCNFTupleEnumeration.tuple_eq_of_shape_value
          (hshape.trans htarget.symm) hhead.symm
        have hselected := hsuccess start middle nb (by simpa [hwords] using hcounter) hbody hi
        have hout := search_retains_selected ports check found accepted value present
          selected copyScratch hc hs tail (by
            rw [← ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs]
            exact hselected)
        rw [hout, ← ExecCNFTupleEnumeration.advanceResult_outside ports middle words selected hc hs]
        exact hselected
      · exact ih (hnext words middle hmiddle) htail

/-- Selection composes the checker's uniform prefix bound with only a local
linear-time copy. The checker may run for exponentially many steps. -/
theorem firstSuccess_fresh_space {R S n B : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a b : StructuredCalls.State R S) (ha : a.stacks selected = [])
    (hc : StructuredCalls.Eval check n
      ((StructuredProgram.Atom.peek selected value found).eval a) b)
    (hchecker : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled check current selected) prefixSteps
        (((StructuredProgram.Atom.peek selected value found).eval a).withPC
          (some (StructuredCalls.compiled check current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ B)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ht : b.stacks scratch = []) :
    ∃ steps c, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a c ∧
      steps ≤ n + 7 * B + 10 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present current selected scratch) current selected)
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present current selected scratch)
            current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ S * B + 8 * B + 10 := by
  let entry := (StructuredProgram.Atom.peek selected value found).eval a
  let save : StructuredCalls.Cmd R S :=
    .seq (.call (StackRoutines.copyProgram current selected scratch value present))
      (.base (.atom (.set found true)))
  let post : StructuredCalls.Cmd R S := .ite accepted save (.base .skip)
  let bound := S * B + 8 * B + 10
  have hB : B ≤ bound := by dsimp [bound]; omega
  have hb : ∀ i, (b.stacks i).length ≤ B :=
    hchecker n _ (Nat.le_refl _) (StructuredCalls.compiled_trace hc current selected)
  have hpost : ∃ m c, StructuredCalls.Eval post m b c ∧ m ≤ 7 * B + 7 := by
    cases hy : b.regs accepted with
    | false => exact ⟨1, b, .ite_false hy (.base (.skip b)), by omega⟩
    | true =>
      let copied : StructuredCalls.State R S :=
        ⟨readRegs b.regs value present none, StackRoutines.copyStacks current selected b.stacks⟩
      have hcopy : StructuredCalls.Eval
          (.call (StackRoutines.copyProgram current selected scratch value present))
          (7 * (b.stacks current).length + 5) b copied :=
        .call _ (ListRegisterProgram.copy_run current selected scratch value present
          hcs hct hts hvp b.regs b.stacks ht)
      let c := (StructuredProgram.Atom.set (s := S) found true).eval copied
      refine ⟨(7 * (b.stacks current).length + 5 + 1) + 1, c,
        .ite_true hy (.seq (n := 7 * (b.stacks current).length + 5) (m := 1)
          hcopy (.base (.atom _ _))), ?_⟩
      have hi := hb current
      omega
  obtain ⟨m, c, hpost, hm⟩ := hpost
  have postBound : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled post current selected) prefixSteps
        (b.withPC (some (StructuredCalls.compiled post current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hinit : dataBits (b.withPC (some (StructuredCalls.compiled post current selected).entry)) ≤
        S * B := StreamResources.dataBits_le_mul _ hb
    have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled post current selected)
      (steps := 7 * B + 7) hinit prefixSteps intermediate (hle.trans hm) htrace i
    dsimp [bound]
    omega
  have checkBound : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled check current selected) prefixSteps
        (entry.withPC (some (StructuredCalls.compiled check current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    exact (hchecker prefixSteps intermediate hle htrace i).trans hB
  have hseq := StructuredSpace.sequence_stack_bound hc hpost current selected checkBound postBound
    (StructuredCalls.compiled (.seq check post) current selected)
    (StructuredCalls.siteAddress (.seq check post)) (StructuredCalls.exitAddress (.seq check post))
    (StructuredCalls.compiled_site _ current selected)
  have hf : entry.regs found = false := by
    simp [entry, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, readRegs, ha]
  have hselect : StructuredCalls.Eval
      (firstSuccessStep check found accepted value present current selected scratch)
      (n + m + 1) entry c := .ite_false hf (.seq hc hpost)
  have selectBound := StructuredSpace.conditional_false_stack_bound hf (.seq hc hpost)
    current selected hseq
    (StructuredCalls.compiled
      (firstSuccessStep check found accepted value present current selected scratch) current selected)
    (StructuredCalls.siteAddress
      (firstSuccessStep check found accepted value present current selected scratch))
    (StructuredCalls.exitAddress
      (firstSuccessStep check found accepted value present current selected scratch))
    (StructuredCalls.compiled_site _ current selected)
  let peek : StructuredCalls.Cmd R S := .base (.atom (.peek selected value found))
  have hp : StructuredCalls.Eval peek 1 a entry := .base (.atom _ _)
  have peekBound : ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace (StructuredCalls.compiled peek current selected) prefixSteps
        (a.withPC (some (StructuredCalls.compiled peek current selected).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hinitial : ∀ i, (a.stacks i).length ≤ B := hchecker 0 _ (Nat.zero_le _) (.refl _)
    have hinit : dataBits (a.withPC (some (StructuredCalls.compiled peek current selected).entry)) ≤
        S * B := StreamResources.dataBits_le_mul _ hinitial
    have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled peek current selected)
      (steps := 1) hinit prefixSteps intermediate hle htrace i
    dsimp [bound]
    omega
  refine ⟨1 + (n + m + 1), c, .seq hp hselect, by omega, ?_⟩
  exact StructuredSpace.sequence_stack_bound hp hselect current selected peekBound selectBound
    (StructuredCalls.compiled
      (firstSuccess check found accepted value present current selected scratch) current selected)
    (StructuredCalls.siteAddress
      (firstSuccess check found accepted value present current selected scratch))
    (StructuredCalls.exitAddress
      (firstSuccess check found accepted value present current selected scratch))
    (StructuredCalls.compiled_site _ current selected)

/-- Later visits retain the first witness with constant time and bounded
space, even though the odometer still traverses the remaining ranks. -/
theorem firstSuccess_saved_space {R S B : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S)
    (a : StructuredCalls.State R S) (hne : a.stacks selected ≠ [])
    (hinitial : ∀ i, (a.stacks i).length ≤ B) :
    ∃ b, StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) 2 a b ∧
      b.stacks = a.stacks ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 2 →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present current selected scratch) current selected)
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present current selected scratch)
            current selected).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ S * B + 8 * B + 10 := by
  obtain ⟨b, heval, hframe⟩ := firstSuccess_saved check found accepted value present
    current selected scratch a hne
  refine ⟨b, heval, hframe, ?_⟩
  intro prefixSteps intermediate hle htrace i
  have hinit : dataBits (a.withPC (some (StructuredCalls.compiled
      (firstSuccess check found accepted value present current selected scratch)
      current selected).entry)) ≤ S * B := StreamResources.dataBits_le_mul _ hinitial
  have h := StructuredSpace.local_stack_bound (StructuredCalls.compiled
    (firstSuccess check found accepted value present current selected scratch) current selected)
    (steps := 2) hinit prefixSteps intermediate hle htrace i
  omega


/-- Complete actual first-success traversal with both resources on its trace.
The callback contract is discharged by the concrete candidate checker; its
uniform prefix bound, rather than its running time, controls loop storage. -/
theorem search_resources {R S : ℕ} (ports : CounterForPrograms.Ports R S)
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (selected copyScratch : Fin S) (d budget boundaryBound callbackBound : ℕ)
    (I : StructuredCalls.State R S → Prop)
    (stable : CounterForPrograms.FrameStable ports (fun _ => I))
    (spec : ExecCNFTupleEnumeration.BodySpec ports
      (firstSuccess check found accepted value present ports.counter selected copyScratch)
      (List.replicate d 2) I budget)
    (hcallback : ∀ words a b nb, words.map List.length = List.replicate d 2 →
      I a → (∀ i, (a.stacks i).length ≤ boundaryBound) →
      a.stacks ports.counter = Encoding.encodeList id words → a.stacks ports.scratch = [] →
      StructuredCalls.Eval
        (firstSuccess check found accepted value present ports.counter selected copyScratch)
        nb a b →
      (∀ i, (b.stacks i).length ≤ boundaryBound) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (StructuredCalls.compiled
          (firstSuccess check found accepted value present ports.counter selected copyScratch)
          ports.counter ports.counter) prefixSteps
          (a.withPC (some (StructuredCalls.compiled
            (firstSuccess check found accepted value present ports.counter selected copyScratch)
            ports.counter ports.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (a : StructuredCalls.State R S) (hi : I a)
    (ha : ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hc : a.stacks ports.counter =
      Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks ports.scratch = []) :
    ∃ steps out, I out ∧ out.stacks ports.scratch = [] ∧
      out.stacks ports.counter = Encoding.encodeList id (List.replicate d [false, false]) ∧
      steps ≤ 4 ^ d * (budget + 42 * d + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program ports
        (firstSuccess check found accepted value present ports.counter selected copyScratch))
        steps (a.withPC (some (ExecCNFTupleEnumeration.program ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch)).entry))
        (out.withPC none) ∧
      (∃ loopSteps, steps = 1 + loopSteps + 1 ∧
        ExecCNFTupleEnumeration.Visits ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch)
          (List.replicate d 2) (List.range' 0 (4 ^ d)) loopSteps
          (ExecCNFTupleEnumeration.startResult ports a) out) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (ExecCNFTupleEnumeration.program ports
          (firstSuccess check found accepted value present ports.counter selected copyScratch))
          prefixSteps (a.withPC (some (ExecCNFTupleEnumeration.program ports
            (firstSuccess check found accepted value present ports.counter selected copyScratch)).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max callbackBound (S * boundaryBound + 7 * (6 * d + 1) + 4) := by
  let body := firstSuccess check found accepted value present ports.counter selected copyScratch
  obtain ⟨n, out, he, hv, ho, _, houtScratch, hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct ports body (List.replicate d 2) I budget
      stable spec (List.replicate d [false, false]) a (by simp) hi hc hs
      (ExecCNFTupleEnumeration.zero_tuple_value d 2)
  have hp : 2 ^ (List.replicate d [false, false]).flatten.length = 4 ^ d := by
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul]
    change 2 ^ (d * 2) = 4 ^ d
    rw [Nat.mul_comm d 2, pow_mul]
    norm_num
  have hlen : (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
    rw [Enumerators.encoded_shape_length (by simp :
      (List.replicate d [false, false]).map List.length = List.replicate d 2)]
    simp
    omega
  let J : StructuredCalls.State R S → Prop := fun state => I state ∧
    (∀ i, (state.stacks i).length ≤ boundaryBound) ∧ state.stacks ports.scratch = []
  have hj : J (ExecCNFTupleEnumeration.startResult ports a) :=
    ⟨stable 0 a _ (fun _ _ _ => rfl) hi, ha, hs⟩
  have hloop := Enumerators.visits_stack_bound ports body (List.replicate d 2)
    J J boundaryBound callbackBound (fun _ h => h.2.1) (fun _ h => h.2.1)
    (by
      intro words start finish nb hw hcounter hbody hJ _
      obtain ⟨m, finish', _, hr, _, hs', hI'⟩ := spec words start hw hJ.1 hcounter hJ.2.2
      have heq := hbody.final_unique ports.counter hr
      subst finish'
      obtain ⟨hb, hprefix⟩ := hcallback words start finish nb hw hJ.1 hJ.2.1
        hcounter hJ.2.2 hbody
      exact ⟨⟨hI', hb, hs'⟩, hs', hprefix⟩)
    (by
      intro words state _ hcounter hJ
      refine ⟨stable 0 state _ (ExecCNFTupleEnumeration.advanceResult_outside ports state words)
        hJ.1, ?_, ExecCNFTupleEnumeration.advanceResult_scratch ports state words⟩
      intro i
      by_cases hcounterPort : i = ports.counter
      · subst i
        rw [ExecCNFTupleEnumeration.advanceResult_counter,
          ExecCNFTupleEnumeration.bumpWords_encoded_length, ← hcounter]
        exact hJ.2.1 ports.counter
      · by_cases hscratchPort : i = ports.scratch
        · subst i
          simp
        · rw [← ExecCNFTupleEnumeration.advanceResult_outside ports state words i
            hcounterPort hscratchPort]
          exact hJ.2.1 i)
    hv hj
  have hspace := Enumerators.enumerate_stack_bound ports body hv hloop
  have hreset := Enumerators.visits_reset_counter hv
    (ExecCNFTupleEnumeration.startResult_flag ports a)
  refine ⟨1 + n + 1, out, ho, houtScratch, ?_, ?_,
    StructuredCalls.compiled_halt_trace he ports.counter ports.counter, ?_, ?_⟩
  · simpa using hreset
  · rw [hp, hlen] at hn
    nlinarith
  · exact ⟨n, rfl, by simpa only [hp] using hv⟩
  · have hsize : 2 * (List.replicate d 2).sum +
        2 * (List.replicate d 2).length + 1 = 6 * d + 1 := by
      simp
      omega
    simpa only [hsize] using hspace


/-- Selection soundness refers to the physical retained matrix, not to an
arbitrary successful element of an abstract family. A preexisting witness is
unchanged; a fresh witness comes from the actual checker's acceptance bit. -/
theorem firstSuccess_matrix_sound {R S steps : ℕ} {Matrix : Type*}
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (current selected scratch matrix : Fin S)
    (valid : Matrix → Prop) (encode : Matrix → List Bool)
    (a out : StructuredCalls.State R S)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (hms : matrix ≠ selected)
    (hold : a.stacks selected ≠ [] → ∃ Q, valid Q ∧ a.stacks matrix = encode Q)
    (hcheck : a.stacks selected = [] → ∃ n b,
      StructuredCalls.Eval check n
        ((StructuredProgram.Atom.peek selected value found).eval a) b ∧
      b.stacks selected = [] ∧ b.stacks scratch = [] ∧
      (b.regs accepted = true → ∃ Q, valid Q ∧ b.stacks matrix = encode Q))
    (heval : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a out) :
    out.stacks selected ≠ [] → ∃ Q, valid Q ∧ out.stacks matrix = encode Q := by
  by_cases ha : a.stacks selected = []
  · obtain ⟨n, b, hc, hs, ht, hvalid⟩ := hcheck ha
    cases hf : b.regs accepted with
    | false =>
        have hr := firstSuccess_fresh_reject check found accepted value present
          current selected scratch a b ha hc hf
        have heq := heval.final_unique current hr
        subst out
        exact fun h => (h hs).elim
    | true =>
        obtain ⟨c, hr, _, hframe⟩ := firstSuccess_fresh_accept check found accepted value present
          current selected scratch a b ha hc hf hcs hct hts hvp ht hs
        have heq := heval.final_unique current hr
        subst out
        intro _
        obtain ⟨Q, hQ, hmatrix⟩ := hvalid hf
        exact ⟨Q, hQ, (hframe matrix hms).trans hmatrix⟩
  · obtain ⟨b, hb, hframe⟩ := firstSuccess_saved check found accepted value present
      current selected scratch a ha
    have heq := heval.final_unique current hb
    subst out
    intro _
    obtain ⟨Q, hQ, hmatrix⟩ := hold ha
    exact ⟨Q, hQ, by rw [hframe]; exact hmatrix⟩


/-- Every callback boundary retains the same polynomial word bound. Only the
matrix being tested and the saved candidate may change; all caller words and
the counter survive selection exactly. -/
theorem firstSuccess_frame {R S steps B : ℕ}
    (check : StructuredCalls.Cmd R S) (found accepted value present : Fin R)
    (current selected scratch matrix : Fin S) (a out : StructuredCalls.State R S)
    (hcs : current ≠ selected) (hct : current ≠ scratch) (hts : scratch ≠ selected)
    (hvp : value ≠ present) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hcheck : a.stacks selected = [] → ∃ n b,
      StructuredCalls.Eval check n
        ((StructuredProgram.Atom.peek selected value found).eval a) b ∧
      b.stacks selected = [] ∧ b.stacks scratch = [] ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      (∀ i, i ≠ matrix → b.stacks i = a.stacks i))
    (heval : StructuredCalls.Eval
      (firstSuccess check found accepted value present current selected scratch) steps a out) :
    (∀ i, (out.stacks i).length ≤ B) ∧
      ∀ i, i ≠ matrix → i ≠ selected → out.stacks i = a.stacks i := by
  by_cases hs : a.stacks selected = []
  · obtain ⟨n, b, hc, hbselected, hbscratch, hb, hframe⟩ := hcheck hs
    cases hf : b.regs accepted with
    | false =>
        have hr := firstSuccess_fresh_reject check found accepted value present
          current selected scratch a b hs hc hf
        have heq := heval.final_unique current hr
        subst out
        exact ⟨hb, fun i hm _ => hframe i hm⟩
    | true =>
        obtain ⟨c, hr, hselected, hcframe⟩ := firstSuccess_fresh_accept check found accepted value
          present current selected scratch a b hs hc hf hcs hct hts hvp hbscratch hbselected
        have heq := heval.final_unique current hr
        subst out
        refine ⟨?_, fun i hm hsel => (hcframe i hsel).trans (hframe i hm)⟩
        intro i
        by_cases hsel : i = selected
        · subst i
          rw [hselected]
          exact hb current
        · rw [hcframe i hsel]
          exact hb i
  · obtain ⟨b, hb, hframe⟩ := firstSuccess_saved check found accepted value present
      current selected scratch a hs
    have heq := heval.final_unique current hb
    subst out
    exact ⟨fun i => by rw [hframe]; exact ha i, fun i _ _ => congrFun hframe i⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

theorem invariant_stable (matrix : Fin 48) (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (base : State 16 48) (B : ℕ) :
    CounterForPrograms.FrameStable counterPorts (fun _ => Invariant matrix Ready Good base B) := by
  intro _ a b hab ha
  have hf (i : Fin 48) (h40 : i ≠ 40) (h41 : i ≠ 41) : b.stacks i = a.stacks i :=
    (hab i h40 h41).symm
  refine ⟨hready a b ha.ready (fun i _ h40 h41 _ => hf i h40 h41), ?_, ?_, ?_⟩
  · intro i h40 h41
    rw [hf i h40 h41]
    exact ha.bound i h40 h41
  · intro hs
    rw [hf matrix hm40 hm41]
    exact ha.sound (by simpa only [hf 42 (by decide) (by decide)] using hs)
  · intro i hm h40 h41 h42
    exact (hf i h40 h41).trans (ha.frame i hm h40 h41 h42)

/-- Every actual first-success callback preserves its semantic witness and
polynomial boundary storage, and includes the complete checker's prefix cost. -/
theorem selection_runs (candidate : Cmd 16 48) (matrix : Fin 48)
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
    (base a : State 16 48) (words : List (List Bool))
    (hw : words.map List.length = List.replicate d 2)
    (ha : Invariant matrix Ready Good base B a)
    (hc : a.stacks 40 = Encoding.encodeList id words) (hs : a.stacks 41 = []) :
    ∃ n out, n ≤ T + 7 * (B + C) + 10 ∧ Eval (selection candidate) n a out ∧
      out.stacks 40 = Encoding.encodeList id words ∧ out.stacks 41 = [] ∧
      Invariant matrix Ready Good base B out ∧
      ∀ k c, k ≤ n → Trace (compiled (selection candidate) 40 40) k
        (a.withPC (some (compiled (selection candidate) 40 40).entry)) c →
        ∀ i, (c.stacks i).length ≤ 56 * (B + C) + 10 := by
  have hab : ∀ i, (a.stacks i).length ≤ B := by
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
  let entry := (StructuredProgram.Atom.peek (42 : Fin 48) (13 : Fin 16) 12).eval a
  have hentry : entry.stacks = a.stacks := rfl
  have hentryReady : Ready entry := hready a entry ha.ready (fun _ _ _ _ _ => rfl)
  have hcheck : ∃ n b, n ≤ T ∧ Eval candidate n entry b ∧
      (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧ (b.regs 15 = true → Good (b.stacks matrix)) ∧
      ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
        (entry.withPC (some (compiled candidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ C :=
    hchecks words entry hw hentryReady hab hc
  have hrun : ∃ n out, n ≤ T + 7 * (B + C) + 10 ∧ Eval (selection candidate) n a out ∧
      ∀ k c, k ≤ n → Trace (compiled (selection candidate) 40 40) k
        (a.withPC (some (compiled (selection candidate) 40 40).entry)) c →
        ∀ i, (c.stacks i).length ≤ 56 * (B + C) + 10 := by
    by_cases hsaved : a.stacks 42 = []
    · obtain ⟨n, b, hn, he, hf, _, _, hp⟩ := hcheck
      have hb45 : b.stacks 45 = [] := (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready)
      have hp' : ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (entry.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ B + C := by
        intro k c hk ht i
        exact (hp k c hk ht i).trans (Nat.le_add_left _ _)
      obtain ⟨steps, out, heval, htime, hspace⟩ := firstSuccess_fresh_space candidate
        12 15 13 14 40 42 45 a b hsaved he hp' (by decide) (by decide) (by decide)
        (by decide) hb45
      refine ⟨steps, out, by omega, heval, ?_⟩
      intro k c hk ht i
      have h := hspace k c hk ht i
      omega
    · obtain ⟨out, he, _, hp⟩ := firstSuccess_saved_space candidate 12 15 13 14 40 42 45 a hsaved hab
      refine ⟨2, out, by omega, he, ?_⟩
      intro k c hk ht i
      have h := hp k c hk ht i
      omega
  obtain ⟨n, out, hn, he, hspace⟩ := hrun
  have hchecksFrame : a.stacks 42 = [] → ∃ n b, Eval candidate n entry b ∧
      b.stacks 42 = [] ∧ b.stacks 45 = [] ∧ (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ i, i ≠ matrix → b.stacks i = a.stacks i := by
    intro h42
    obtain ⟨n, b, _, he, hf, hb, _, _⟩ := hcheck
    exact ⟨n, b, he, (hf 42 (Ne.symm hm42)).trans h42,
      (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready), hb, hf⟩
  obtain ⟨hbound, hframe⟩ := firstSuccess_frame candidate 12 15 13 14 40 42 45 matrix a out
    (by decide) (by decide) (by decide) (by decide) hab hchecksFrame he
  have hsound := firstSuccess_matrix_sound candidate 12 15 13 14 40 42 45 matrix Good id a out
    (by decide) (by decide) (by decide) (by decide) hm42
    (fun h => ⟨a.stacks matrix, ha.sound h, rfl⟩)
    (by
      intro h42
      obtain ⟨n, b, _, he, hf, _, hgood, _⟩ := hcheck
      exact ⟨n, b, he, (hf 42 (Ne.symm hm42)).trans h42,
        (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready),
        fun h => ⟨b.stacks matrix, hgood h, rfl⟩⟩) he
  refine ⟨n, out, hn, he, (hframe 40 (Ne.symm hm40) (by decide)).trans hc,
    (hframe 41 (Ne.symm hm41) (by decide)).trans hs, ?_, hspace⟩
  refine ⟨hready a out ha.ready (fun i hm _ _ h42 => hframe i hm h42),
    fun i _ _ => hbound i, ?_, ?_⟩
  · intro h
    obtain ⟨word, hgood, hword⟩ := hsound h
    simpa only [hword, id_eq] using hgood
  · intro i hm h40 h41 h42
    exact (hframe i hm h42).trans (ha.frame i hm h40 h41 h42)


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

/-- A complete concrete candidate scan, including every failed attempt and
the final overflow reset. Target acceptance is later supplied by the existing
local-code and graph existence mathematics and the actual typed checker. -/
theorem core_runs_oai (candidate : Cmd 16 48) (matrix : Fin 48)
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
    (base a : State 16 48) (ha : Invariant matrix Ready Good base B a)
    (hc : a.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks 41 = []) :
    ∃ n out, n ≤ 4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 ∧
      Trace (core candidate) n (a.withPC (some (core candidate).entry)) (out.withPC none) ∧
      Invariant matrix Ready Good base B out ∧ out.stacks 41 = [] ∧
      out.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) ∧
      out.stacks 42 ≠ [] ∧ Good (out.stacks matrix) ∧
      ∀ k c, k ≤ n → Trace (core candidate) k
        (a.withPC (some (core candidate).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4) := by
  let I := Invariant matrix Ready Good base B
  have stable := invariant_stable matrix hm40 hm41 Ready Good hready base B
  have spec : ExecCNFTupleEnumeration.BodySpec counterPorts (selection candidate)
      (List.replicate d 2) I (T + 7 * (B + C) + 10) := by
    intro words start hw hi hcurrent hscratch
    obtain ⟨n, out, hn, he, hc', hs', hi', _⟩ := selection_runs candidate matrix
      hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap hchecks
      base start words hw hi hcurrent hscratch
    exact ⟨n, out, hn, he, hc', hs', hi'⟩
  have hab := invariant_full_bound matrix Ready Good base a d B hcap ha
    (List.replicate d [false, false]) (by simp) hc hs
  obtain ⟨n, out, houtI, houtScratch, houtCounter, hn, htrace, hlog, hspace⟩ :=
    search_resources counterPorts candidate 12 15 13 14 42 45 d
      (T + 7 * (B + C) + 10) B (56 * (B + C) + 10) I stable spec
      (by
        intro words start finish nb hw hi _ hcurrent hscratch heval
        obtain ⟨m, finish', _, hr, hc', hs', hi', hp⟩ := selection_runs candidate matrix
          hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap hchecks
          base start words hw hi hcurrent hscratch
        have hnm := StreamResources.eval_steps_eq 40 42 heval hr
        have heq := heval.final_unique 40 hr
        subst finish'
        subst m
        exact ⟨invariant_full_bound matrix Ready Good base finish d B hcap hi' words hw hc' hs', hp⟩)
      a ha hab hc hs
  obtain ⟨loopSteps, _, hv⟩ := hlog
  have hmember : CounterPrograms.value target.flatten ∈ List.range' 0 (4 ^ d) := by
    have hlen : target.flatten.length = 2 * d := by
      rw [List.length_flatten, htarget, List.sum_replicate, smul_eq_mul]
      omega
    have hp : 2 ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
    have hlt := ExecCNFTupleOdometer.value_lt_power_length target.flatten
    rw [hlen, hp] at hlt
    simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hlt
  let J : State 16 48 → Prop := fun state => I state ∧ state.stacks 41 = []
  have hstart : J (ExecCNFTupleEnumeration.startResult counterPorts a) :=
    ⟨stable 0 a _ (fun _ _ _ => rfl) ha, hs⟩
  have hselected := search_reaches_success counterPorts candidate 12 15 13 14 42 45
    (by decide) (by decide) hv J hstart
    (by
      intro words start finish nb hw hcurrent heval hJ
      obtain ⟨m, finish', _, hr, _, hs', hi'⟩ := spec words start hw hJ.1 hcurrent hJ.2
      have heq := heval.final_unique 40 hr
      subst finish'
      exact ⟨hi', hs'⟩)
    (by
      intro words start hJ
      exact ⟨stable 0 start _ (ExecCNFTupleEnumeration.advanceResult_outside counterPorts start words)
        hJ.1, ExecCNFTupleEnumeration.advanceResult_scratch counterPorts start words⟩)
    target htarget hmember (by
      intro start finish nb hcurrent heval hJ
      by_cases hsaved : start.stacks 42 = []
      · let entry := (StructuredProgram.Atom.peek (42 : Fin 48) (13 : Fin 16) 12).eval start
        have heReady : Ready entry := hready start entry hJ.1.ready (fun _ _ _ _ _ => rfl)
        have heBound := invariant_full_bound matrix Ready Good base start d B hcap
          hJ.1 target htarget hcurrent hJ.2
        obtain ⟨m, b, hr, hyes⟩ := haccept entry heReady heBound hcurrent
        obtain ⟨m', b', _, hr', hf, _, _, _⟩ := hchecks target entry htarget heReady heBound hcurrent
        have heq := hr.final_unique 40 hr'
        subst b'
        have hb45 : b.stacks 45 = [] := (hf 45 (Ne.symm hm45)).trans (hcopy start hJ.1.ready)
        have hb42 : b.stacks 42 = [] := (hf 42 (Ne.symm hm42)).trans hsaved
        obtain ⟨saved, hsave, hword, _⟩ := firstSuccess_fresh_accept candidate 12 15 13 14 40 42 45
          start b hsaved hr hyes (by decide) (by decide) (by decide) (by decide) hb45 hb42
        have heq' := heval.final_unique 40 hsave
        subst finish
        rw [hword, hf 40 (Ne.symm hm40)]
        change start.stacks counterPorts.counter ≠ []
        rw [hcurrent]
        cases target <;> simp [Encoding.encodeList]
      · obtain ⟨saved, hsave, hframe⟩ := firstSuccess_saved candidate 12 15 13 14 40 42 45 start hsaved
        have heq := heval.final_unique 40 hsave
        subst finish
        simpa only [hframe] using hsaved)
  exact ⟨n, out, hn, htrace, houtI, houtScratch, houtCounter, hselected,
    houtI.sound hselected, hspace⟩


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs_oai
