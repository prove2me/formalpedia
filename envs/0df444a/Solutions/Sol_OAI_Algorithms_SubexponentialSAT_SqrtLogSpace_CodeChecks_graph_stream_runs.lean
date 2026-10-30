-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:03:10.50927+00:00
-- url     : https://prove2.me/submissions/3d67b1e2-c22e-4b23-9b2b-cf1edab201c8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphWordCallback_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_rejection_scan_runs_space

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

/-- The binary graph search uses the same width-two scalar format. -/
theorem binary_digit_sound (x : Bool × Bool) (hx : invalidDigit false x = false) :
    ∃ a : ZMod 2, digitBits x = scalarBits a := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b
  · exact ⟨0, by
      unfold scalarBits
      have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx
  · exact ⟨1, by
      unfold scalarBits
      have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
      rw [hw]
      decide⟩
  · simp [invalidDigit] at hx


theorem binary_digit_complete (x : Bool × Bool) (a : ZMod 2)
    (ha : digitBits x = scalarBits a) : invalidDigit false x = false := by
  have hw : scalarWidth 2 = 2 := by norm_num [scalarWidth]
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

theorem binary_digits_sound (xs : List (Bool × Bool))
    (hvalid : xs.any (invalidDigit false) = false) :
    ∃ v : Fin xs.length → ZMod 2, xs.map digitBits = fieldWords v := by
  apply digits_sound
  intro x hx
  apply binary_digit_sound
  have h := List.any_eq_false.mp hvalid x hx
  exact Bool.eq_false_iff.mpr h


/-- The same assertion includes both scalar values of the graph alphabet. -/
theorem binary_field_valid (xs : List (Bool × Bool)) (v : Fin xs.length → ZMod 2)
    (h : xs.map digitBits = fieldWords v) : xs.any (invalidDigit false) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : digitBits x ∈ fieldWords v := h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [binary_digit_complete x (v i) hi.symm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyCharacters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real Walsh characters of the Boolean cube, with unnormalized Fourier sums. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, bitSign, eq_self, ite_true, if_true, one_mul]
  by_cases hb : b = 0
  · subst b
    simp only [add_zero, bitSign, eq_self, ite_true, if_true, mul_one]
  have ha1 : a = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    have hlt := a.val_lt
    omega
  have hb1 : b = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
    have hlt := b.val_lt
    omega
  have hab : a + b = 0 := by
    rw [ha1, hb1]
    exact CharTwo.add_self_eq_zero 1
  unfold bitSign
  rw [ite_eq_left hab, ite_eq_right ha, ite_eq_right hb]
  norm_num

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceParity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Walsh testing using a mod-two matrix product and natural-number counters. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem bitSign_sum {ι : Type*} (t : Finset ι) (f : ι → ZMod 2) :
    bitSign (∑ i ∈ t, f i) = ∏ i ∈ t, bitSign (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, bitSign_add, ih]

theorem character_parity {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) (i : Fin D) :
    character a (s i) = bitSign (parityProducts s a i) := by
  unfold character parityProducts
  rw [bitSign_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [mul_comm]

theorem characterInt_parity {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) (i : Fin D) :
    characterInt a (s i) = 1 - 2 * (if parityProducts s a i ≠ 0 then (1 : ℤ) else 0) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  push_cast
  rw [characterInt_cast, character_parity]
  by_cases h : parityProducts s a i = 0 <;> norm_num [bitSign, h]

theorem walshInt_eq_sub_twice_weight {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) :
    walshInt s a = (D : ℤ) - 2 * parityWeight s a := by
  unfold walshInt
  simp_rw [characterInt_parity]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hh : (∑ i : Fin D, if parityProducts s a i ≠ 0 then (1 : ℤ) else 0) =
      parityWeight s a := by
    rw [← Finset.sum_filter]
    simp [parityWeight]
  rw [hh]
  simp

theorem int_abs_bound_iff_nat_checks (q D h : ℕ) :
    (q : ℤ) * |(D : ℤ) - 2 * h| ≤ D ↔
      q * D ≤ D + 2 * q * h ∧ 2 * q * h ≤ q * D + D := by
  have he : |(q : ℤ) * ((D : ℤ) - 2 * h)| = (q : ℤ) * |(D : ℤ) - 2 * h| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
  rw [← he, abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have h1 : (q : ℤ) * D ≤ D + 2 * q * h := by nlinarith
    have h2 : (2 : ℤ) * q * h ≤ q * D + D := by nlinarith
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (q : ℤ) * D ≤ D + 2 * q * h := by exact_mod_cast h1
    have h2' : (2 : ℤ) * q * h ≤ q * D + D := by exact_mod_cast h2
    constructor <;> nlinarith

theorem good_iff_parity_checks {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) :
    Good q s ↔ ∀ a, a ≠ 0 →
      q * D ≤ D + 2 * q * parityWeight s a ∧
        2 * q * parityWeight s a ≤ q * D + D := by
  unfold Good
  simp_rw [walshInt_eq_sub_twice_weight, int_abs_bound_iff_nat_checks]

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem no_graph_rejection_iff {r D : ℕ} (s : Fin D → Cayley.Cube r) (q : ℕ) :
    (∀ x, ¬ graphWordRejects s x q) ↔ WalshExistence.Good q s := by
  rw [WalshExistence.good_iff_parity_checks]
  constructor
  · intro h x hx
    by_contra hbad
    exact h x ⟨hx, hbad⟩
  · intro h x hx
    exact hx.2 (h x hx.1)

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

/-- A valid streamed character is checked by the original bit arithmetic. Only
the one-bit rejection latch changes; this includes every off-port caller stack. -/
theorem graph_stream_body_valid {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x)
    (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
    (a : ScanState) (b : Bool)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hpayload : a.stacks 34 = []) (htmp : a.stacks 35 = [])
    (hcounter : a.stacks 36 = CodeCandidates.tupleBits xs)
    (hlatch : a.stacks 37 = [b]) (hcopy : a.stacks 39 = []) :
    ∃ steps out, steps ≤ graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24 ∧
      Eval graphStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 37 [b || decide (graphWordRejects s x q)] := by
  have hlen : xs.length = r := by simpa using congrArg List.length hfields
  obtain ⟨c, hconvert, hflag, hcopy', hword, hcframe⟩ :=
    copy_convert_eval false 36 39 34 35 (by decide) (by decide) (by decide) (by decide)
      xs a hcounter hcopy hpayload htmp
  have hlow (i : Fin 34) : c.stacks ⟨i.val, by omega⟩ = a.stacks ⟨i.val, by omega⟩ := by
    apply hcframe <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp only at hv <;> omega
  have hwork : GraphWorkEmpty (projectState id graphStreamStacks c) := by
    intro i
    exact (hlow ⟨i.val, by omega⟩).trans (he i)
  have h35 : c.stacks 35 = [] := (hcframe 35 (by decide) (by decide)).trans htmp
  have h34 : c.stacks 34 = (scalarFrames (List.ofFn x)).reverse := by
    rw [hword, pair_frames_eq xs x hfields]
  obtain ⟨n, small, hn, hrun, hworkout, hreject, _, _, h34out, hframe⟩ :=
    graphWordCallback_eval s x q qbits Dbits hqv hDv
      (projectState id graphStreamStacks c) hwork
      ((hlow 29).trans hm) ((hlow 30).trans ht) ((hlow 31).trans hq)
      ((hlow 32).trans hD) h35 h34
  let middle := embedState id graphStreamStacks c small
  have hcall := eval_call_from_state graphCallbackProgram id graphStreamStacks c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hrun 34 34)
  have hmid (i : Fin 36) : middle.stacks (graphStreamStacks i) = small.stacks i :=
    embedState_stack id graphStreamStacks c small (Fin.castAdd_injective _ _) i
  have hmidreg : middle.regs 15 = decide (graphWordRejects s x q) :=
    (embedState_register id graphStreamStacks c small Function.injective_id 15).trans hreject
  have hstacks : middle.stacks = a.stacks := by
    funext i
    by_cases hi : i.val < 29
    · let j : Fin 29 := ⟨i.val, hi⟩
      have hij : graphStreamStacks (graphWordStacks j) = i := Fin.ext rfl
      rw [← hij, hmid, hworkout j]
      exact (he j).symm
    · by_cases h34i : i = 34
      · subst i
        exact (hmid 34).trans (h34out.trans hpayload.symm)
      · by_cases hi36 : i.val < 36
        · let j : Fin 36 := ⟨i.val, hi36⟩
          have hij : graphStreamStacks j = i := Fin.ext rfl
          have hj34 : j ≠ 34 := by
            intro h
            apply h34i
            exact Fin.ext (by simpa [j] using congrArg Fin.val h)
          have h39i : i ≠ 39 := by
            intro h
            have hv := congrArg Fin.val h
            omega
          rw [← hij, hmid]
          exact (hframe j (by change 29 ≤ i.val; omega) hj34).trans (hcframe i h39i h34i)
        · have houter : middle.stacks i = c.stacks i := by
            apply embedState_stack_frame
            rintro ⟨j, hj⟩
            have hv := congrArg Fin.val hj
            change j.val = i.val at hv
            omega
          rw [houter]
          by_cases h39i : i = 39
          · subst i
            exact hcopy'.trans hcopy.symm
          · exact hcframe i h39i h34i
  obtain ⟨out, hor, hout, houtframe⟩ :=
    latchReject_eval 37 middle b ((congrFun hstacks 37).trans hlatch)
  refine ⟨(58 * xs.length + 16) + (n + 1 + 3 + 1), out, ?_, ?_, ?_⟩
  · rw [hlen]
    omega
  · exact hconvert.seq (Eval.ite_false (hflag.trans hvalid) (hcall.seq hor))
  · funext i
    by_cases hi : i = 37
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

/-- The binary graph domain is checked in the same bounded-memory scan; padded
high-bit candidates are charged and physically discarded. -/
theorem graph_stream_body {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (words : List (List Bool)) (hshape : words.map List.length = List.replicate r 2)
    (a : ScanState) (b : Bool)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hpayload : a.stacks 34 = []) (htmp : a.stacks 35 = [])
    (hcounter : a.stacks 36 = Encoding.encodeList id words)
    (hlatch : a.stacks 37 = [b]) (hcopy : a.stacks 39 = []) :
    ∃ steps out, steps ≤ graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24 ∧
      Eval graphStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 37
        [b || rejectedRank (fun x => graphWordRejects s x q) (CounterPrograms.value words.flatten)] := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words r hshape
  have hc : a.stacks 36 = CodeCandidates.tupleBits xs := by
    rw [tupleBits_eq, hwords]
    exact hcounter
  subst r
  cases hv : xs.any (CodeCandidates.invalidDigit false) with
  | false =>
      obtain ⟨x, hx⟩ := CodeCandidates.binary_digits_sound xs hv
      obtain ⟨steps, out, hn, hrun, hout⟩ := graph_stream_body_valid s x q qbits Dbits hqv hDv
        xs hx hv a b he hm ht hq hD hpayload htmp hc hlatch hcopy
      refine ⟨steps, out, hn, hrun, ?_⟩
      rw [← hwords, hx, rejectedRank_field]
      exact hout
  | true =>
      have hrejected : rejectedRank (fun x => graphWordRejects s x q)
          (CounterPrograms.value words.flatten) = false := by
        apply rejectedRank_invalid
        · have hw : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
            norm_num [SubexpEnumerationPayload.scalarWidth]
          simpa only [hw] using hshape
        · intro x hx
          have hvalid := CodeCandidates.binary_field_valid xs x (hwords.trans hx)
          rw [hv] at hvalid
          contradiction
      obtain ⟨out, hrun, hout⟩ := invalid_conversion_eval false 36 39 34 35
        (.seq (.call (ProgramLinking.liftProgram graphCallbackProgram id graphStreamStacks))
          (latchReject 37)) (by decide) (by decide) (by decide) (by decide)
        xs a hc hcopy hpayload htmp hv
      refine ⟨68 * xs.length + 20, out, by omega, hrun, ?_⟩
      rw [hrejected, Bool.or_false, hout, ← hlatch, Function.update_eq_self]

/-- The Walsh iterator likewise uses the actual graph arithmetic on every
valid character, and physically clears every invalid padded word. -/
theorem graph_rejection_body {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (base : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks base))
    (hm : base.stacks 29 = matrixFrames s) (ht : base.stacks 30 = List.replicate D true)
    (hq : base.stacks 31 = qbits) (hD : base.stacks 32 = Dbits)
    (hp : base.stacks 34 = []) (htmp : base.stacks 35 = []) (hcopy : base.stacks 39 = []) :
    RejectionBody graphCounterPorts 37 graphStreamBody r
      (graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24) base
      (rejectedRank (fun x => graphWordRejects s x q)) := by
  constructor
  intro words a hw ha hc _
  have hlo (i : Fin 36) : a.stacks (graphStreamStacks i) = base.stacks (graphStreamStacks i) := by
    apply ha.1
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [graphStreamStacks, graphCounterPorts] at hv
      omega
  obtain ⟨b, hb⟩ := ha.2
  obtain ⟨n, out, hn, hr, ho⟩ := graph_stream_body s q qbits Dbits hqv hDv words hw a b
    (fun i => (hlo (graphWordStacks i)).trans (he i))
    ((hlo 29).trans hm) ((hlo 30).trans ht) ((hlo 31).trans hq) ((hlo 32).trans hD)
    ((hlo 34).trans hp) ((hlo 35).trans htmp) hc hb
    ((ha.1 39 (by decide) (by decide) (by decide)).trans hcopy)
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

/-- The actual Walsh scan similarly decides Good for every supplied graph,
including failed candidates and the zero-dimensional character space. -/
theorem graph_stream_runs_oai {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcopy : a.stacks 39 = [])
    (hcounter : a.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]))
    (hscratch : a.stacks 38 = []) (hlatch : a.stacks 37 = [false])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
      Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
        (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
        (out.withPC none) ∧ RejectionFrame graphCounterPorts 37 a out ∧ out.stacks 38 = [] ∧
      (out.stacks 37 = [false] ↔ WalshExistence.Good q s) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max (B + graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
              (40 * B + 7 * (6 * r + 1) + 4)) := by
  obtain ⟨n, out, hn, htrace, hf, hs, hl, hspace⟩ := rejection_scan_runs_space
    graphCounterPorts 37 (by decide) (by decide) graphStreamBody r
    (graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
    (rejectedRank (fun x => graphWordRejects s x q)) a false
    (graph_rejection_body s q qbits Dbits hqv hDv a he hm ht hq hD hp htmp hcopy)
    hcounter hscratch hlatch B hB ha
  refine ⟨n, out, ?_, htrace, hf, hs, ?_, ?_⟩
  · simpa only [graphStreamBudget, stream_body_budget] using hn
  · rw [hl]
    simp only [Bool.false_or, List.cons.injEq, and_true]
    rw [no_rejectedRank_iff (by norm_num [SubexpEnumerationPayload.scalarWidth])]
    exact no_graph_rejection_iff s q
  · simpa only [Nat.add_assoc] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs_oai
