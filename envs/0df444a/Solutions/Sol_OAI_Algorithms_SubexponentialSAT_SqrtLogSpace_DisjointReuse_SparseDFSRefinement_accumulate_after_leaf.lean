-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:34:29.925556+00:00
-- url     : https://prove2.me/submissions/b9a172af-6398-4648-ba88-b93b7c6486d9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseAccumulatorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A fixed finite binary accumulator with actual source traces and local prefixSteps bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator

open BitProgram StructuredCalls

theorem command_eval (regs : Fin 8 → Bool) (left right : List Bool) :
    ∃ t final,
      t ≤ 33 * (max left.length right.length + 1) + 30 ∧
      Eval command t (state regs left right) final ∧
      final.stacks 0 = binaryNat (CounterPrograms.value left + CounterPrograms.value right) ∧
      final.stacks 1 = [] ∧ final.stacks 2 = [] := by
  let regs₀ := Function.update regs 0 false
  let word := BinaryArithmetic.add left right
  obtain ⟨rf, ta, hta, htrace⟩ := BinaryPrograms.Add.littleEndian_run regs₀ left right
  let middle := state rf word []
  have hadd : Eval (.call BinaryPrograms.Add.littleEndianProgram) ta
      (state regs₀ left right) middle := by
    apply Eval.call
    simpa only [state, middle, regs₀, word, BinaryArithmetic.add,
      StructuredProgram.State.withPC, Function.update_self,
      show BinaryPrograms.Add.littleEndianProgram.entry = 0 by rfl] using htrace
  obtain ⟨tn, htn, hnormal⟩ := CanonicalWordProgram.normalizeUnsigned_call registers
    (Function.Embedding.refl (Fin 3)) middle (rf ∘ registers) word
  have hstart : embedState registers id middle
      (CanonicalWordProgram.state (rf ∘ registers) word []) = middle := by
    apply embedState_eq_of_ports registers id middle middle _ registers.injective
      Function.injective_id
    · intro i
      rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact (hi ⟨i, rfl⟩).elim
  change Eval (.call (ProgramLinking.liftProgram CanonicalWordProgram.normalizeUnsignedProgram
    registers id)) tn (embedState registers id middle
      (CanonicalWordProgram.state (rf ∘ registers) word []))
    (embedState registers id middle
      (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
        (binaryNat (CounterPrograms.value word)) [])) at hnormal
  rw [hstart] at hnormal
  have hreset : Eval (.base (.atom (.set (0 : Fin 8) false))) 1
      (state regs left right) (state regs₀ left right) :=
    .base (.atom _ _)
  have hlength := BinaryArithmetic.length_add left right
  refine ⟨1 + (ta + tn), _, ?_, hreset.seq (hadd.seq hnormal), ?_, ?_, ?_⟩
  · dsimp [word] at htn
    omega
  · calc
      _ = binaryNat (CounterPrograms.value word) :=
        embedState_stack registers id _ _ Function.injective_id (0 : Fin 3)
      _ = _ := by
        simp only [word, CounterPrograms.value_eq_toNat, BinaryArithmetic.toNat_add]
  · exact embedState_stack registers id _ _ Function.injective_id (1 : Fin 3)
  · exact embedState_stack registers id _ _ Function.injective_id (2 : Fin 3)

theorem program_runs (regs : Fin 8 → Bool) (left right : List Bool) :
    ∃ final : StructuredProgram.State 8 3,
      RunsIn program (33 * (max left.length right.length + 1) + 31)
        ((state regs left right).withPC (some program.entry)) (final.withPC none) ∧
      final.stacks 0 = binaryNat (CounterPrograms.value left + CounterPrograms.value right) ∧
      final.stacks 1 = [] ∧ final.stacks 2 = [] := by
  obtain ⟨t, final, ht, he, houtput, h1, h2⟩ := command_eval regs left right
  exact ⟨final, ⟨t + 1, by omega, compiled_halt_trace he 0 0⟩, houtput, h1, h2⟩

/-- The runtime bound is linear in both input word lengths, so this local
trace-growth estimate is polynomial independently of the number of leaves. -/
theorem prefix_dataBits_le (regs : Fin 8 → Bool) (left right : List Bool)
    (prefixSteps : ℕ) (c : Cfg 8 3 (StructuredCalls.size command + 1))
    (hp : prefixSteps ≤ 33 * (max left.length right.length + 1) + 31)
    (htrace : Trace program prefixSteps
      ((state regs left right).withPC (some program.entry)) c) :
    dataBits c ≤ left.length + right.length +
      33 * (max left.length right.length + 1) + 31 := by
  have h := trace_dataBits program htrace
  have hstart : dataBits ((state regs left right).withPC (some program.entry)) =
      left.length + right.length := by
    simp [dataBits, stackBits, state, BinaryPrograms.Add.stackState, Fin.sum_univ_succ]
  rw [hstart] at h
  omega

/-- The same actual accumulator execution returns the canonical sum and has
linear all-prefix source-stack space whenever the sum is an `n`-variable count. -/
theorem canonical_execution (regs : Fin 8 → Bool) (a b n : ℕ) (hcount : a + b ≤ 2 ^ n) :
    ∃ (t : ℕ) (final : StructuredProgram.State 8 3),
      t ≤ 100 * (n + 1) ∧
      Trace program t
        ((state regs (binaryNat a) (binaryNat b)).withPC (some program.entry))
        (final.withPC none) ∧
      final.stacks 0 = binaryNat (a + b) ∧ final.stacks 1 = [] ∧ final.stacks 2 = [] ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace program prefixSteps
          ((state regs (binaryNat a) (binaryNat b)).withPC (some program.entry)) c →
          dataBits c ≤ 100 * (n + 1) := by
  have ha : a ≤ 2 ^ n := (Nat.le_add_right a b).trans hcount
  have hb : b ≤ 2 ^ n := (Nat.le_add_left b a).trans hcount
  have hla := binaryNat_length_le ha
  have hlb := binaryNat_length_le hb
  have hva : CounterPrograms.value (binaryNat a) = a := by
    rw [← CanonicalWordProgram.ofDigits_eq_value, binaryNat_decode]
  have hvb : CounterPrograms.value (binaryNat b) = b := by
    rw [← CanonicalWordProgram.ofDigits_eq_value, binaryNat_decode]
  obtain ⟨final, ⟨t, ht, htrace⟩, houtput, h1, h2⟩ :=
    program_runs regs (binaryNat a) (binaryNat b)
  refine ⟨t, final, by omega, htrace, ?_, h1, h2, ?_⟩
  · simpa only [hva, hvb] using houtput
  · intro prefixSteps c hp hc
    have hs := prefix_dataBits_le regs (binaryNat a) (binaryNat b) prefixSteps c
      (hp.trans ht) hc
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

private theorem stackBits_single_le {S : ℕ} (words : Fin S → List Bool) (i : Fin S) :
    (words i).length ≤ stackBits words :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((words j).length)) (Finset.mem_univ i)

private theorem lifted_call_space {r s l steps localBound frameBound : ℕ}
    (routine : Program r s l) (register : Fin r ↪ Fin 80) (stack : Fin s ↪ Fin 1220)
    (frame : Data) {a b : State r s}
    (htrace : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hlocal : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        prefixSteps ((embedState register stack frame a).withPC
          (some (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  have hsource := StructuredSpace.liftProgram_stack_bound routine register stack
    (frame.withPC none) register.injective stack.injective htrace hlocal hframe
  have he := eval_call_lifted routine register stack frame register.injective stack.injective htrace
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (ProgramLinking.liftProgram routine register stack)
        (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        (siteAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (exitAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (compiled_site (.call (ProgramLinking.liftProgram routine register stack)) 256 256) ht
      simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
        StructuredProgram.State.withPC, id_eq] using hsource

/-- The root accumulator uses the same concrete addition/normalization trace.
The disjoint-mass premise bounds both canonical input words; the final count
is on physical port260 and both count scratch ports are empty. -/
theorem accumulate_execution_space (frame : Data) (regs : Fin 8 → Bool)
    (a b n frameBound : ℕ) (hcount : a + b ≤ 2 ^ n)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ 100 * (n + 1), ∃ e,
      Eval accumulate t
        (embedState (registers 8 (by decide)) countStack frame
          (SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b))) e ∧
      e.stacks 260 = binaryNat (a + b) ∧ e.stacks 263 = [] ∧ e.stacks 30 = [] ∧
      (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = frame.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled accumulate 256 256) prefixSteps
          ((embedState (registers 8 (by decide)) countStack frame
            (SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b))).withPC
              (some (compiled accumulate 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) frameBound := by
  obtain ⟨t, final, ht, htrace, houtput, hclear1, hclear2, hprefix⟩ :=
    SparseCountProgram.Accumulator.canonical_execution regs a b n hcount
  refine ⟨t, ht, embedState (registers 8 (by decide)) countStack frame final,
    eval_call_lifted SparseCountProgram.Accumulator.program (registers 8 (by decide))
      countStack frame (registers 8 (by decide)).injective countStack.injective htrace,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 0).trans houtput
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 1).trans hclear1
  · exact (embedState_stack (registers 8 (by decide)) countStack frame final
      countStack.injective 2).trans hclear2
  · intro i h0 h1 h2
    apply embedState_stack_frame
    rintro ⟨j, rfl⟩
    fin_cases j
    · exact h0 rfl
    · exact h1 rfl
    · exact h2 rfl
  · apply lifted_call_space SparseCountProgram.Accumulator.program
      (registers 8 (by decide)) countStack frame htrace _ hframe
    intro prefixSteps c hp hc i
    exact (stackBits_single_le c.stacks i).trans (hprefix prefixSteps c hp hc)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}


theorem accumulate_after_leaf_oai (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total bound : ℕ) (d : SparseDFSProgram.Data)
    (hpending : d.stacks 257 = pendingBytes rest)
    (hheader : d.stacks 258 = Encoding.encodeNat n)
    (hthreshold : d.stacks 259 = threshold)
    (htotal : d.stacks 260 = binaryNat total)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hleaf : d.stacks 263 = binaryNat (rawCount node.formula))
    (hscratch : d.stacks 30 = [])
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ 100 * (n + 1), ∃ e,
      Eval SparseDFSProgram.accumulate t d e ∧
      AfterVisit threshold ⟨rest, total + rawCount node.formula⟩ e ∧
      (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.accumulate 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.accumulate 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) bound := by
  let regs := d.regs ∘ SparseDFSProgram.registers 8 (by decide)
  have hp : projectState (SparseDFSProgram.registers 8 (by decide)) SparseDFSProgram.countStack d =
      SparseCountProgram.Accumulator.state regs (binaryNat total) (binaryNat (rawCount node.formula)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact htotal
    · exact hleaf
    · exact hscratch
  obtain ⟨t, ht, e, he, ho, hzero, _, hf, hspace⟩ :=
    SparseDFSResource.accumulate_execution_space d regs total (rawCount node.formula) n bound hcount hbound
  rw [← hp, embedState_project _ _ d (SparseDFSProgram.registers 8 (by decide)).injective
    SparseDFSProgram.countStack.injective] at he hspace
  refine ⟨t, ht, e, he, ?_, hf, hspace⟩
  exact ⟨(hf 257 (by decide) (by decide) (by decide)).trans hpending,
    (hf 258 (by decide) (by decide) (by decide)).trans hheader,
    (hf 259 (by decide) (by decide) (by decide)).trans hthreshold,
    ho, (hf 261 (by decide) (by decide) (by decide)).trans hleft,
    (hf 262 (by decide) (by decide) (by decide)).trans hright, hzero⟩


open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf_oai
