-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:33:18.170365+00:00
-- url     : https://prove2.me/submissions/4ecb2f33-b009-4767-af0e-07bcad153f94

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMarkedReturn_trace_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

private theorem digits_two_eq_map_toNat (n : ℕ) :
    Nat.digits 2 n = n.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction n.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem binaryNat_decode (n : ℕ) :
    Nat.ofDigits 2 ((binaryNat n).map Bool.toNat) = n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rw [binaryNat, ite_eq_right hn, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 n

/-- A decoded word with the canonical terminal bit is the specified binary output. -/
theorem eq_binaryNat_of_decode {word : List Bool} {n : ℕ}
    (hd : Nat.ofDigits 2 (word.map Bool.toNat) = n)
    (hc : word = [false] ∨ ∃ initialBits : List Bool, word = initialBits ++ [true]) :
    word = binaryNat n := by
  rcases hc with rfl | ⟨initialBits, rfl⟩
  · have hn : n = 0 := hd.symm
    simp [hn]
  · have hn : n ≠ 0 := by
      intro hz
      have hzero := hd.trans hz
      exact Nat.one_ne_zero (Nat.digits_zero_of_eq_zero (b := 2) (by decide)
        hzero 1 (by simp))
    have hdigits := Nat.digits_ofDigits 2 (by decide)
      ((initialBits ++ [true]).map Bool.toNat)
      (by
        intro digit hmem
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hmem
        exact Bool.toNat_lt b)
      (by intro h; simp)
    rw [hd] at hdigits
    apply (List.map_injective_iff.mpr (Function.LeftInverse.injective Bool.ofNat_toNat))
    rw [binaryNat, ite_eq_right hn, ← digits_two_eq_map_toNat]
    exact hdigits.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical unsigned binary output by a fixed finite word program.
The program reverses its input, removes high zeroes, reverses back, and emits
one false bit in the empty case. All source stack prefixes have a linear local
bound. No algebraic construction is imported to implement normalization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

open BitProgram StructuredCalls CounterPrograms

theorem dropZeroes_length (xs : List Bool) : (dropZeroes xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [dropZeroes]; omega

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp [value, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

theorem ofDigits_eq_value (word : List Bool) :
    Nat.ofDigits 2 (word.map Bool.toNat) = value word := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [List.map_cons, Nat.ofDigits_cons, value, ih]

theorem normalized_eq_binaryNat (word : List Bool) :
    normalized word = binaryNat (value word) := by
  induction word using List.reverseRecOn with
  | nil => simp [normalized, dropZeroes, nonemptyWord, binaryNat_zero]
  | append_singleton word b ih =>
    cases b with
    | false => simpa [normalized, List.reverse_append, dropZeroes, value_append, value] using ih
    | true =>
      apply eq_binaryNat_of_decode
      · have hn : normalized (word ++ [true]) = word ++ [true] := by
          simp [normalized, List.reverse_append, dropZeroes, nonemptyWord]
        rw [hn]
        exact ofDigits_eq_value _
      · right
        exact ⟨word, by simp [normalized, List.reverse_append, dropZeroes, nonemptyWord]⟩

theorem reset_eval (regs : Fin 3 → Bool) (word : List Bool) :
    Eval reset 3 (state regs word []) (state zeroRegs word []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs word [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply CounterForPrograms.data_ext
  · funext i
    fin_cases i <;> simp [state, zeroRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  · rfl

theorem test_eval (regs : Fin 3 → Bool) (xs : List Bool) :
    Eval test 3 (state regs [] xs) (tested xs) := by
  have h := (StructuredProgram.Eval.atom (.peek (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (state regs [] xs)).seq
    ((StructuredProgram.Eval.atom (.bnot (2 : Fin 3) (0 : Fin 3)) _).seq
      (StructuredProgram.Eval.atom (.band (2 : Fin 3) (2 : Fin 3) (1 : Fin 3)) _))
  apply Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply CounterForPrograms.data_ext
  · funext i
    cases xs with
    | nil => fin_cases i <;> simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    | cons b xs => cases b <;> fin_cases i <;>
        simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  · rfl

theorem dropBody_eval (xs : List Bool) :
    Eval dropBody 4 (tested (false :: xs)) (tested xs) := by
  have h := StructuredProgram.Eval.atom (.pop (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (tested (false :: xs))
  have he : (StructuredProgram.Atom.pop (1 : Fin 3) 0 1).eval (tested (false :: xs)) =
      state (counterRegs false true true) [] xs := by
    apply CounterForPrograms.data_ext
    · funext i
      fin_cases i <;> simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    · funext i
      fin_cases i <;> simp [tested, state, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact (Eval.base h).seq (test_eval _ xs)

theorem dropLoop_eval (xs : List Bool) :
    ∃ n, n ≤ 5 * xs.length + 1 ∧ Eval dropLoop n (tested xs) (tested (dropZeroes xs)) := by
  induction xs with
  | nil => exact ⟨1, by simp, Eval.while_false rfl⟩
  | cons b xs ih =>
    cases b with
    | true => exact ⟨1, by simp, Eval.while_false rfl⟩
    | false =>
      obtain ⟨n, hn, he⟩ := ih
      exact ⟨4 + n + 1, by simp only [List.length_cons]; omega,
        Eval.while_true rfl (dropBody_eval xs) he⟩

theorem transfer_eval (d : Data) (src dst : Fin 3) (h : src ≠ dst) :
    Eval (.call (StackRoutines.transferProgram src dst 0 1))
      (3 * (d.stacks src).length + 3) d (transferred d src dst) :=
  Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks)

theorem emitZero_eval (regs : Fin 3 → Bool) :
    Eval emitZero 5 (state regs [] []) (state zeroRegs [false] []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs [] [])).seq
    (StructuredProgram.Eval.atom (.push (0 : Fin 3) (0 : Fin 3)) _)
  have he : (StructuredProgram.Atom.push (0 : Fin 3) 0).eval
      ((StructuredProgram.Atom.set (0 : Fin 3) false).eval (state regs [] [])) =
      state (Function.update regs 0 false) [false] [] := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact (Eval.base h).seq (reset_eval _ _)

theorem finish_eval (regs : Fin 3 → Bool) (xs : List Bool) :
    ∃ n, n ≤ 7 ∧ Eval finish n (state regs xs []) (state zeroRegs (nonemptyWord xs) []) := by
  have h := StructuredProgram.Eval.atom (.peek (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (state regs xs [])
  have he : (StructuredProgram.Atom.peek (0 : Fin 3) 0 1).eval (state regs xs []) =
      state (readRegs regs 0 1 xs.head?) xs [] := rfl
  rw [he] at h
  cases xs with
  | nil => exact ⟨7, by decide, (Eval.base h).seq (Eval.ite_false (by simp [state, readRegs])
      (emitZero_eval _))⟩
  | cons b xs => exact ⟨5, by decide, (Eval.base h).seq
      (Eval.ite_true (by simp [state, readRegs]) (reset_eval _ _))⟩

theorem normalizeUnsigned_eval (regs : Fin 3 → Bool) (word : List Bool) :
    ∃ n, n ≤ 17 * word.length + 28 ∧ Eval normalizeUnsigned n
      (state regs word []) (state zeroRegs (binaryNat (value word)) []) := by
  let first := readRegs regs 0 1 none
  have hfirst : transferred (state regs word []) 0 1 = state first [] word.reverse := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [transferred, state, StackRoutines.transferStacks]
  have h1 := transfer_eval (state regs word []) 0 1 (by decide)
  rw [hfirst] at h1
  have h2 := test_eval first word.reverse
  obtain ⟨n, hn, h3⟩ := dropLoop_eval word.reverse
  have h4 := transfer_eval (tested (dropZeroes word.reverse)) 1 0 (by decide)
  let lastRegs := readRegs (tested (dropZeroes word.reverse)).regs 0 1 none
  have hlast : transferred (tested (dropZeroes word.reverse)) 1 0 =
      state lastRegs (dropZeroes word.reverse).reverse [] := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [transferred, tested, state, StackRoutines.transferStacks]
  rw [hlast] at h4
  obtain ⟨m, hm, h5⟩ := finish_eval lastRegs (dropZeroes word.reverse).reverse
  have hout : nonemptyWord (dropZeroes word.reverse).reverse = binaryNat (value word) :=
    normalized_eq_binaryNat word
  rw [hout] at h5
  refine ⟨(3 * word.length + 3) + (3 + (n +
      ((3 * (dropZeroes word.reverse).length + 3) + m))), ?_, ?_⟩
  · have hl := dropZeroes_length word.reverse
    simp only [List.length_reverse] at hn hl
    omega
  · exact h1.seq (h2.seq (h3.seq (h4.seq h5)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

end SubexponentialSAT.SqrtLog.LeafOuterProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual per-mark staging and return adapters. Each reference is copied and
reversed into the frontend marker words. Each completed high-assignment count
is moved to the marked collector, with its temporary words reclaimed and parser
registers reset by real instructions. Fresh high-query setup remains mandatory. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter

open BitProgram StructuredCalls SqrtLog LeafOuterProgram

theorem finish_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval finish (finishSteps a) a (finishState a) := by
  have hr := route_eval (788,323) (by unfold routeValid; decide) a ht
  have hc := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 cleanupPorts
    (by decide) (routed (788,323) a).regs (routed (788,323) a).stacks
    (by simpa [routed] using ht)
  have hp := Eval.base (SubexpParameterProgram.atoms_eval
    [.set (16 : Fin 40) false, .set 17 true, .set 18 false]
    (clearState (routed (788,323) a)))
  exact hr.seq (hc.seq hp)

theorem finishState_stacks (a : Data) :
    (finishState a).stacks = BankRoutines.clearBankStacks cleanupPorts
      (Function.update a.stacks 323 (a.stacks 788)) := by
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace CanonicalHigh
open DisjointReuse

theorem result_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result a).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,rfl⟩
  fin_cases j <;> simp_all [stackMap]

theorem command_eval (a : Data) (h793 : a.stacks 793=[]) (h794 : a.stacks 794=[]) :
    ∃ steps, steps≤17*(a.stacks 788).length+29 ∧ Eval command steps a (result a) := by
  obtain ⟨steps,hbound,he⟩ := CanonicalWordProgram.normalizeUnsigned_eval
    (a.regs ∘ regMap) (a.stacks 788)
  have hp : projectState regMap stackMap a =
      CanonicalWordProgram.state (a.regs ∘ regMap) (a.stacks 788) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [stackMap, h793, h794]
  have ht := compiled_halt_trace he 0 0
  rw [← hp] at ht
  exact ⟨steps+1,by omega,eval_call_from_state CanonicalWordProgram.normalizeUnsignedProgram
    regMap stackMap a (Fin.castAdd_injective _ _) (by decide) ht⟩

open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem reset_eval (a : Data) :
    Eval reset (2*(a.stacks 793).length+2*(a.stacks 794).length+6) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (793 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_call_eval (794 : Fin 896) (0 : Fin 40) 1
    (readRegs a.regs 0 1 none) (clearStacks 793 a.stacks)
  have h := h1.seq h2
  simp only [clearStacks_frame 793 794 a.stacks (by decide),readRegs_reset] at h
  convert h using 1
  · rfl
  · omega
  · rfl

/-- Canonicalizes the actual complete high accumulator on the same bounded
source run. Zero is the singleton false word, never an empty output. -/
theorem trace_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), Trace program steps (a.withPC (some program.entry))
      ((result (resetState a)).withPC none) ∧ steps≤21*bound+36 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤917*bound+36 := by
  have hm : (resetState a).stacks 788=a.stacks 788 := by simp [resetState,clearStacks]
  obtain ⟨steps,hbound,he⟩ := command_eval (resetState a)
    (by simp [resetState,clearStacks]) (by simp [resetState,clearStacks])
  rw [hm] at hbound
  have ht : (2*(a.stacks 793).length+2*(a.stacks 794).length+6)+steps+1≤21*bound+36 := by
    have := hb 793
    have := hb 794
    have := hb 788
    omega
  have hx := (reset_eval a).seq he
  refine ⟨_,compiled_halt_trace hx 788 788,ht,?_⟩
  have hin : dataBits (a.withPC (some program.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hspace := StructuredSpace.local_stack_bound program (steps:=21*bound+36) hin
    prefixSteps intermediate (Nat.le_trans hle ht) htrace i
  omega

theorem final_width (a : Data) (n : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788)≤2^n) :
    ((result (resetState a)).stacks 788).length≤n+1 := by
  rw [final_count]
  exact countWord_length_le hcount

theorem final_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result (resetState a)).stacks i=a.stacks i := by
  rw [result_frame _ i h788 h793 h794]
  simp [resetState,clearStacks,h793,h794]

end CanonicalHigh


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

theorem cleanupPorts_eq :
    cleanupPorts =
      (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)) :=
  cleanupPortsWrapped.2

@[simp] theorem mem_cleanupPorts (i : Fin 768) :
    i∈cleanupPorts ↔ ¬Protected i ∧ i≠699 := by
  rw [cleanupPorts_eq]
  simp

theorem cleanupPorts_nodup : cleanupPorts.Nodup :=
  cleanupPorts_eq.symm ▸ (List.nodup_finRange 768).filter _

theorem cleanup_eval (a : Data) : Eval cleanup (cleanupCost a) a (cleaned a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 699 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 699 0 1))
      (2*(a.stacks 699).length+3) a mid :=
    Eval.call _ (ListRegisterProgram.clear_run (699 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 := BankRoutines.clear_eval (699 : Fin 768) (0 : Fin 40) 1 cleanupPorts
    cleanupPorts_nodup mid.regs mid.stacks (by simp [mid])
  have hm : cleanupPorts.map (fun i => (mid.stacks i).length)=
      cleanupPorts.map (fun i => (a.stacks i).length) := by
    apply List.map_congr_left
    intro i hi
    have hn := (mem_cleanupPorts i).mp hi
    simp [mid,hn.2]
  rw [hm] at h2
  have hf : (⟨readRegs mid.regs 0 1 none,
      BankRoutines.clearBankStacks cleanupPorts mid.stacks⟩ : Data)=cleaned a := by
    simp [mid,cleaned,StackRoutines.readRegs_reset]
  rw [hf] at h2
  have he := h1.seq h2
  have hk : (2*(a.stacks 699).length+3)+
      (2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum+3*cleanupPorts.length+3)=
      cleanupCost a := by
    unfold cleanupCost
    omega
  rw [hk] at he
  exact he

theorem cleaned_stacks (a : Data) (i : Fin 768) :
    (cleaned a).stacks i=if Protected i then a.stacks i else [] := by
  by_cases hp : Protected i
  · have hn : i≠699 := by
      intro h
      subst i
      exact (by decide : ¬Protected (699 : Fin 768)) hp
    simp [cleaned,BankRoutines.clearBankStacks,hp,hn]
  · by_cases hn : i=699
    · subst i
      simp [cleaned,BankRoutines.clearBankStacks,show ¬Protected (699 : Fin 768) from by decide]
    · simp [cleaned,BankRoutines.clearBankStacks,hp,hn]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog

@[simp] theorem cleaned_lower (a : Data) (i : Fin 768) :
    (cleaned a).stacks (stackMap i)=
      if LeafProgram.Query.Protected i then a.stacks (stackMap i) else [] := by
  rw [cleaned,result_stack,LeafProgram.Query.cleaned_stacks]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

theorem upperPorts_eq :
    upperPorts =
      (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)) :=
  upperPortsWrapped.2

@[simp] theorem mem_upperPorts (i : Fin 896) :
    i ∈ upperPorts ↔ 832 ≤ i.val ∧ i.val < 895 := by
  rw [upperPorts_eq]
  simp

theorem upperPorts_nodup : upperPorts.Nodup :=
  upperPorts_eq.symm ▸ (List.nodup_finRange 896).filter _

theorem lower_eval (a : Data) : Eval HighMarkedFrontend.cleanupCommand
    (LeafProgram.Query.cleanupCost (HighMarkedFrontend.project a)+1) a
    (HighMarkedFrontend.cleaned a) := by
  exact eval_call_from_state HighMarkedFrontend.cleanupLocalProgram id HighMarkedFrontend.stackMap a
    Function.injective_id (Fin.castAdd_injective _ _)
    (compiled_halt_trace (LeafProgram.Query.cleanup_eval (HighMarkedFrontend.project a)) 699 323)

theorem upper_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval upperClear (upperCost a) a (upperCleared a) := by
  simpa only [upperClear,upperCost,upperCleared] using BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 upperPorts upperPorts_nodup
    a.regs a.stacks ht

theorem reset_eval (a : Data) : Eval resetParser 3 a (parserReset a) :=
  Eval.base (SubexpParameterProgram.atoms_eval
    [.set (16 : Fin 40) false,.set 17 true,.set 18 false] a)

theorem eval (a : Data) (ht : a.stacks 767=[]) : Eval command (cost a) a (result a) := by
  have hfinish := finish_eval a ht
  have hlower := lower_eval (finishState a)
  have hscratch : (HighMarkedFrontend.cleaned (finishState a)).stacks 767=[] := by
    rw [show (767 : Fin 896)=HighMarkedFrontend.stackMap 767 from rfl,
      HighMarkedFrontend.cleaned_lower]
    simp [LeafProgram.Query.Protected,finishState_stacks,BankRoutines.clearBankStacks,
      cleanupPorts,ht,HighMarkedFrontend.stackMap]
  exact hfinish.seq (hlower.seq ((upper_eval _ hscratch).seq (reset_eval _)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete outer count execution. The final canonicalization and marked
return consume the entire accumulated binary count. Their compact boundary is
proved separately from the transient workspace used by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution

open OAI BitProgram StructuredCalls HighQueryAdapter DisjointReuse
open HashGreedyProgram.NativeRound

theorem canonicalized_frame (a : Data) (i : Fin 896)
    (h788 : i ≠ 788) (h793 : i ≠ 793) (h794 : i ≠ 794) :
    (canonicalized a).stacks i = a.stacks i := CanonicalHigh.final_frame a i h788 h793 h794

/-- No transient query cap is fed back into the retained-word bound. -/
theorem canonicalized_bound (a : Data) (n B : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ B)
    (hframe : ∀ i, i ≠ 788 → i ≠ 793 → i ≠ 794 → (a.stacks i).length ≤ B) :
    ∀ i, ((canonicalized a).stacks i).length ≤ B := by
  intro i
  by_cases hc : i = 788
  · subst i
    exact (CanonicalHigh.final_width a n hcount).trans hn
  · by_cases hs : i = 793
    · subst i
      rw [(canonicalized_scratch a).1]
      exact Nat.zero_le _
    · by_cases ht : i = 794
      · subst i
        rw [(canonicalized_scratch a).2]
        exact Nat.zero_le _
      · rw [canonicalized_frame a i hc hs ht]
        exact hframe i hc hs ht

/-- Actual canonicalization and cleanup on the same run, with an independent
all-prefix cap. This local suffix has no evaluator or successful-layout input. -/
theorem markedReturn_trace_space_oai (a : Data) (n D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ D)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, Eval markedReturn steps a (returned a) ∧
      steps + 1 ≤ 3421 * D + 5136 ∧
      Trace (compiled markedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled markedReturn 778 777).entry)) ((returned a).withPC none) ∧
      StageSpace markedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨nc,hcanonical,hnc,hcanonicalSpace⟩ := CanonicalHigh.trace_space a D hD
  have hec : Eval canonicalize nc a (canonicalized a) := Eval.call _ hcanonical
  have hcb : ∀ i, ((canonicalized a).stacks i).length ≤ D :=
    canonicalized_bound a n D hcount hn (fun i _ _ _ => hD i)
  have hct : (canonicalized a).stacks 767 = [] :=
    (canonicalized_frame a 767 (by decide) (by decide) (by decide)).trans ht
  have her := HashMarkedReturn.eval (canonicalized a) hct
  obtain ⟨_,hrcost,hrspace⟩ := HashMarkedReturn.trace_space (canonicalized a) D hcb hct
  have he : Eval markedReturn (nc + HashMarkedReturn.cost (canonicalized a)) a (returned a) :=
    hec.seq her
  have hcspace : StageSpace canonicalize nc a (931 * D + 54) := by
    constructor
    apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site canonicalize 778 777) hcanonical
    intro k z hk hz i
    have hi := hcanonicalSpace k z hk hz i
    omega
  have hrspace' : StageSpace HashMarkedReturn.command
      (HashMarkedReturn.cost (canonicalized a)) (canonicalized a) (931 * D + 54) :=
    ⟨fun k z hk hz => hrspace.bound k z (by omega) hz⟩
  have hseq := hcspace.seq hec her hrspace'
  refine ⟨_,he,by omega,compiled_halt_trace he 778 777,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hseq.bound⟩

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space_oai
