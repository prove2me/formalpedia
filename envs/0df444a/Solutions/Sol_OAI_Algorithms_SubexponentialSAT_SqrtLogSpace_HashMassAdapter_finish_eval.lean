-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finish_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:40:44.708002+00:00
-- url     : https://prove2.me/submissions/1b58b94d-f5ab-4746-b14c-6d2577c4c7af

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

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

theorem binaryNat_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (binaryNat a).length ≤ n + 1 := by
  by_cases hzero : a = 0
  · simp [binaryNat, hzero]
  · simpa only [binaryNat, ite_eq_right hzero, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

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

theorem normalizeUnsigned_call {R S : ℕ}
    (register : Fin 3 ↪ Fin R) (stack : Fin 3 ↪ Fin S)
    (frame : State R S) (regs : Fin 3 → Bool) (word : List Bool) :
    ∃ n, n ≤ 17 * word.length + 29 ∧
      Eval (.call (ProgramLinking.liftProgram normalizeUnsignedProgram register stack)) n
        (embedState register stack frame (state regs word []))
        (embedState register stack frame
          (state zeroRegs
            (binaryNat (value word)) [])) := by
  obtain ⟨n, hn, he⟩ := normalizeUnsigned_eval regs word
  exact ⟨n + 1, by omega,
    eval_call_lifted normalizeUnsignedProgram register stack frame
      register.injective stack.injective (StructuredCalls.compiled_halt_trace he 0 0)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

variable {X Row : Type*} [Fintype X] {m : ℕ}

theorem normalize_eval (a : Data) (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = []) :
    ∃ n ≤ 17 * (a.stacks 322).length + 29, ∃ b, Eval normalize n a b ∧
      b.stacks = Function.update a.stacks 322
        (DisjointReuse.binaryNat (BinaryArithmetic.toNat (a.stacks 322))) := by
  let regs := fun i => a.regs (normalizeRegisters i)
  let localState := DisjointReuse.CanonicalWordProgram.state regs (a.stacks 322) []
  have hp : projectState normalizeRegisters normalizeStacks a = localState := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i
      · rfl
      · exact h323
      · exact h324
  have hi : embedState normalizeRegisters normalizeStacks a localState = a := by
    rw [← hp]
    exact embedState_project _ _ a normalizeRegisters.injective normalizeStacks.injective
  obtain ⟨n, hn, he⟩ := DisjointReuse.CanonicalWordProgram.normalizeUnsigned_call
    normalizeRegisters normalizeStacks a regs (a.stacks 322)
  rw [hi] at he
  refine ⟨n, hn, _, he, ?_⟩
  change Function.extend normalizeStacks _ a.stacks = _
  have hl : (DisjointReuse.CanonicalWordProgram.state
      DisjointReuse.CanonicalWordProgram.zeroRegs
      (DisjointReuse.binaryNat (CounterPrograms.value (a.stacks 322))) []).stacks =
      Function.update localState.stacks 0
        (DisjointReuse.binaryNat (CounterPrograms.value (a.stacks 322))) := by
    first | done | (funext i; fin_cases i <;> rfl)
  rw [hl, ProgramLinking.extend_update normalizeStacks.injective]
  have hf : Function.extend normalizeStacks localState.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks hi
  rw [hf, CounterPrograms.value_eq_toNat]
  rfl

theorem finish_eval_oai (a : Data) (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (ht : a.stacks 767 = []) (L : ℕ)
    (hacc : (a.stacks 322).length ≤ L) (hscore : (a.stacks 769).length ≤ L) :
    ∃ n ≤ 50 * (L + 1), ∃ b, Eval finish n a b ∧ b.stacks = finishedStacks a := by
  obtain ⟨nn, hnn, b, hn, hb⟩ := normalize_eval a h323 h324
  have hr := LeafOuterProgram.route_eval (322,769)
    (by unfold LeafOuterProgram.routeValid; decide) b (by simp [hb, ht])
  let c := LeafOuterProgram.routed (322,769) b
  have hc := BankRoutines.clear_call_eval (322 : Fin 896) (0 : Fin 40) 1 c.regs c.stacks
  have hcanon : (DisjointReuse.binaryNat (BinaryArithmetic.toNat (a.stacks 322))).length ≤ L + 1 := by
    have hv := (ModularArithmetic.toNat_lt_pow_length (a.stacks 322)).le
    exact (DisjointReuse.binaryNat_length_le hv).trans (by omega)
  refine ⟨nn + (LeafOuterProgram.routeCost (322,769) b + (2 * (c.stacks 322).length + 3)),
    ?_, _, hn.seq (hr.seq hc), ?_⟩
  · simp only [LeafOuterProgram.routeCost, c, LeafOuterProgram.routed, hb,
      Function.update_self, Function.update_of_ne (by decide : (769 : Fin 896) ≠ 322),
      Function.update_of_ne (by decide : (322 : Fin 896) ≠ 769)]
    omega
  · funext i
    by_cases h322 : i = 322 <;> by_cases h769 : i = 769 <;>
      simp [finishedStacks, StackRoutines.clearStacks, c, LeafOuterProgram.routed,
        hb, h322, h769]


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finish_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finish_eval_oai
