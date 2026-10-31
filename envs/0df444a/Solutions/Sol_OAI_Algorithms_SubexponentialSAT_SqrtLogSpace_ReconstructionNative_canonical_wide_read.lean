-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:10.215037+00:00
-- url     : https://prove2.me/submissions/f08a8b64-8ba1-42b0-8dd6-25c5657ebea6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionSpace_readback_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 8 11

theorem stackMap_injective : Function.Injective stackMap := by decide

theorem install_project (a : Data) : install a (project a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, regMap j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_register regMap stackMap a (project a) regMap_injective j
    · exact embedState_register_frame regMap stackMap a (project a) i h
  · funext i
    by_cases h : ∃ j, stackMap j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_stack regMap stackMap a (project a) stackMap_injective j
    · exact embedState_stack_frame regMap stackMap a (project a) i h

theorem move_eval (a : Data) (ha : a.stacks 324 = []) :
    Eval moveCommand (6 * (a.stacks 261).length + 6) a (afterMove a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 261 324 a.stacks⟩
  have h1 := ListRegisterProgram.transfer_run (261 : Fin 330) 324 (0 : Fin 19) 1
    (by decide) (by decide) a.regs a.stacks
  have h2 := ListRegisterProgram.transfer_run (324 : Fin 330) 323 (0 : Fin 19) 1
    (by decide) (by decide) (readRegs a.regs 0 1 none)
    (StackRoutines.transferStacks 261 324 a.stacks)
  have e1 : Eval (.call (StackRoutines.transferProgram 261 324 0 1))
      (3 * (a.stacks 261).length + 3) a mid := Eval.call _ h1
  have e2 : Eval (.call (StackRoutines.transferProgram 324 323 0 1))
      (3 * (mid.stacks 324).length + 3) mid
      ⟨readRegs mid.regs 0 1 none, StackRoutines.transferStacks 324 323 mid.stacks⟩ :=
    Eval.call _ h2
  have he := Eval.seq e1 e2
  convert he using 1 <;>
    simp [ afterMove, mid, StackRoutines.transferStacks,
      ha, StackRoutines.readRegs_reset] ; omega

theorem afterMove_frame (a : Data) (i : Fin 330) (h1 : i ≠ 261) (h2 : i ≠ 323) (h3 : i ≠ 324) :
    (afterMove a).stacks i = a.stacks i := by
  simp [afterMove, StackRoutines.transferStacks, h1, h2, h3]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

theorem normalize_readback_eval (regs : Fin 8 → Bool)
    (word modulus width : List Bool) :
    ∃ finalRegs steps, steps ≤ 17*word.length+29 ∧
      Eval normalizeReadback steps
        (SubexpFlatCount.start regs modulus width word)
        (SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat (BinaryArithmetic.toNat word))) := by
  let initialState := SubexpFlatCount.start regs modulus width word
  let localInput := DisjointReuse.CanonicalWordProgram.state
    (regs ∘ normalizationPorts) word []
  let localOutput := DisjointReuse.CanonicalWordProgram.state
    DisjointReuse.CanonicalWordProgram.zeroRegs
    (DisjointReuse.binaryNat (CounterPrograms.value word)) []
  have hproject : projectState normalizationPorts normalizationPorts initialState =
      localInput := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> rfl
  obtain ⟨steps, hsteps, hrun⟩ :=
    DisjointReuse.CanonicalWordProgram.normalizeUnsigned_call
      normalizationPorts normalizationPorts initialState
      (regs ∘ normalizationPorts) word
  change Eval normalizeReadback steps
    (embedState normalizationPorts normalizationPorts initialState localInput)
    (embedState normalizationPorts normalizationPorts initialState localOutput) at hrun
  rw [← hproject, embedState_project _ _ _ normalizationPorts.injective
    normalizationPorts.injective] at hrun
  let finalState := embedState normalizationPorts normalizationPorts initialState localOutput
  have hstack : finalState.stacks = SubexpFlatCount.store
      (DisjointReuse.binaryNat (BinaryArithmetic.toNat word)) modulus [] width := by
    funext i
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi⟩
      have hij : normalizationPorts j = i := Fin.ext rfl
      rw [← hij]
      change (embedState normalizationPorts normalizationPorts initialState localOutput).stacks
          (normalizationPorts j) = _
      rw [embedState_stack _ _ _ _ normalizationPorts.injective]
      clear_value j
      clear hij hi i
      fin_cases j <;>
        simp [localOutput, DisjointReuse.CanonicalWordProgram.state,
          normalizationPorts, SubexpFlatCount.store, CounterPrograms.value_eq_toNat]
    · have hframe : ¬ ∃ j, normalizationPorts j = i := by
        rintro ⟨j, hj⟩
        apply hi
        rw [← hj]
        exact j.isLt
      change (embedState normalizationPorts normalizationPorts initialState localOutput).stacks i = _
      rw [embedState_stack_frame _ _ _ _ i hframe]
      fin_cases i <;> simp_all [initialState, SubexpFlatCount.start, SubexpFlatCount.store]
  have hfinal : finalState = SubexpFlatCount.start finalState.regs modulus width
      (DisjointReuse.binaryNat (BinaryArithmetic.toNat word)) := by
    exact congrArg₂ StructuredProgram.State.mk rfl hstack
  refine ⟨finalState.regs, steps, hsteps, ?_⟩
  change Eval normalizeReadback steps initialState finalState at hrun
  rwa [hfinal] at hrun

/-- Native reconstruction readback returns precisely the frozen binary word.
The same trace has polynomial local time and bounds every source stack at
every prefix, including modulus, width, and normalization scratch. -/
theorem canonical_readback_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = baseWidth 3 t)
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ finalRegs steps, steps ≤ 600*(S+1)^2 ∧
      Trace canonicalReadbackProgram steps
        ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
          (some canonicalReadbackProgram.entry))
        ((SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat count)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace canonicalReadbackProgram prefixSteps
          ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
            (some canonicalReadbackProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
            600*(S+1)^2 := by
  obtain ⟨readerRegs, word, readerSteps, hvalue, hlength, hsteps, hreader, _⟩ :=
    readback_run_space t ht hd a M cache x count hcount hx regs modulus width hm hw
      S hB hmodulus hinput
  obtain ⟨finalRegs, normalSteps, hnormalSteps, hnormal⟩ :=
    normalize_readback_eval readerRegs word modulus width
  rw [hvalue] at hnormal
  have heval : Eval canonicalReadback (readerSteps+normalSteps)
      (SubexpFlatCount.start regs modulus width (RingProgram.flat x))
      (SubexpFlatCount.start finalRegs modulus width (DisjointReuse.binaryNat count)) :=
    (Eval.call LeafProgram.Readback.countProgram hreader).seq hnormal
  have hbudget : readerSteps+normalSteps+1 ≤ 600*(S+1)^2 := by
    rw [hlength] at hnormalSteps
    nlinarith only [hsteps, hnormalSteps, hB, hmodulus]
  refine ⟨finalRegs, readerSteps+normalSteps+1, hbudget,
    compiled_halt_trace heval 0 0, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (steps := 600*(S+1)^2)
    (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

theorem readback_input_bits (regs : Fin 8 → Bool) (input modulus width : List Bool) :
    stackBits (SubexpFlatCount.start regs modulus width input).stacks =
      input.length + modulus.length + width.length := by
  simp [stackBits, SubexpFlatCount.start, SubexpFlatCount.store, Fin.sum_univ_succ,
    Nat.add_assoc]

theorem canonical_query_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
    (a : LeafProgram.QueryReadback.Data) (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t) (hw : width.length = baseWidth 3 t)
    (ready : LeafProgram.QueryReadback.project a =
      SubexpFlatCount.start regs modulus width (RingProgram.flat x))
    (hs : a.stacks 323 = []) (ha : a.stacks 324 = [])
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ steps b, steps+1 ≤ 4400*(S+1)^2 ∧
      Eval canonicalQueryCommand steps a b ∧
      Trace canonicalQueryProgram (steps+1)
        (a.withPC (some canonicalQueryProgram.entry)) (b.withPC none) ∧
      b.stacks 323 = DisjointReuse.binaryNat count ∧ b.stacks 324 = [] ∧
      (∀ i, (¬ ∃ j, LeafProgram.QueryReadback.stackMap j = i) →
        i ≠ 323 → i ≠ 324 → b.stacks i = a.stacks i) ∧
      (∃ finalRegs : Fin 8 → Bool, b = LeafProgram.QueryReadback.afterMove
        (LeafProgram.QueryReadback.install a (SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat count)))) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace canonicalQueryProgram prefixSteps
          (a.withPC (some canonicalQueryProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks + 4400*(S+1)^2 := by
  obtain ⟨finalRegs, readSteps, hreadSteps, htrace, hlocal⟩ :=
    canonical_readback_run_space t ht hd model M cache x count hcount hx
      regs modulus width hm hw S hB hmodulus hinput
  let localFinal := SubexpFlatCount.start finalRegs modulus width (DisjointReuse.binaryNat count)
  let middle := LeafProgram.QueryReadback.install a localFinal
  have hread : Eval canonicalQueryReadCommand readSteps a middle := by
    have hh := eval_call_lifted canonicalReadbackProgram
      LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap a
      LeafProgram.QueryReadback.regMap_injective LeafProgram.QueryReadback.stackMap_injective htrace
    change Eval canonicalQueryReadCommand readSteps
      (LeafProgram.QueryReadback.install a
        (SubexpFlatCount.start regs modulus width (RingProgram.flat x))) middle at hh
    rw [← ready, LeafProgram.QueryReadback.install_project] at hh
    exact hh
  have hframe : ∀ i, (¬ ∃ j, LeafProgram.QueryReadback.stackMap j = i) →
      middle.stacks i = a.stacks i := by
    intro i hi
    exact embedState_stack_frame _ _ _ _ i hi
  have hs' : middle.stacks 323 = [] := (hframe 323 (by decide)).trans hs
  have ha' : middle.stacks 324 = [] := (hframe 324 (by decide)).trans ha
  have hword : middle.stacks 261 = DisjointReuse.binaryNat count :=
    embedState_stack LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap
      a localFinal LeafProgram.QueryReadback.stackMap_injective 0
  have hlength := hlocal readSteps _ le_rfl htrace (0 : Fin 8)
  change (DisjointReuse.binaryNat count).length ≤
    stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
      600*(S+1)^2 at hlength
  rw [readback_input_bits, hw] at hlength
  have heval := hread.seq (LeafProgram.QueryReadback.move_eval middle ha')
  have hbudget : readSteps+(6*(middle.stacks 261).length+6)+1 ≤ 4400*(S+1)^2 := by
    rw [hword]
    nlinarith only [hreadSteps, hlength, hB, hmodulus, hinput]
  refine ⟨readSteps+(6*(middle.stacks 261).length+6),
    LeafProgram.QueryReadback.afterMove middle, hbudget, heval,
    compiled_halt_trace heval 261 323, ?_, LeafProgram.QueryReadback.afterMove_scratch _, ?_,
    ⟨finalRegs, rfl⟩, ?_⟩
  · rw [LeafProgram.QueryReadback.afterMove_output _ hs' ha', hword]
  · intro i hi hi323 hi324
    have hi261 : i ≠ 261 := by
      intro h
      apply hi
      exact ⟨0, h.symm⟩
    rw [LeafProgram.QueryReadback.afterMove_frame _ _ hi261 hi323 hi324]
    exact hframe i hi
  · intro prefixSteps intermediate hprefix hp
    exact StructuredSpace.local_stack_bound _ (steps := 4400*(S+1)^2)
      (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 19 21
theorem stackMap_injective : Function.Injective stackMap := Fin.castAdd_injective 330 438

theorem install_project (a : Data) : install a (project a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, regMap j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_register regMap stackMap a (project a) regMap_injective j
    · exact embedState_register_frame regMap stackMap a (project a) i h
  · funext i
    by_cases h : ∃ j, stackMap j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_stack regMap stackMap a (project a) stackMap_injective j
    · exact embedState_stack_frame regMap stackMap a (project a) i h

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

/-- The physically staged scalar is decoded and normalized by the same actual
fixed reader, embedded identically into lower330 of the768-stack workspace. -/
theorem canonical_wide_read_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
    (a : Data) (hvalue : a.stacks 261 = RingProgram.flat x)
    (hm : BinaryArithmetic.toNat (a.stacks 194) = 3^t)
    (hw : (a.stacks 202).length = baseWidth 3 t)
    (hempty : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i = [])
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : (a.stacks 194).length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ (steps : ℕ) (regs : Fin 8 → Bool), steps ≤ 4400*(S+1)^2 ∧
      Eval canonicalWideRead steps a
        (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count)) := by
  let q := LeafProgram.QueryReadback.Wide.project a
  have hs : q.stacks 323 = [] := hempty 323 (by simp)
  have ha : q.stacks 324 = [] := hempty 324 (by simp)
  have hr : LeafProgram.QueryReadback.project q =
      SubexpFlatCount.start (q.regs ∘ LeafProgram.QueryReadback.regMap)
        (a.stacks 194) (a.stacks 202) (RingProgram.flat x) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [LeafProgram.QueryReadback.stackMap,q,
          LeafProgram.QueryReadback.Wide.project,LeafProgram.QueryReadback.Wide.stackMap,
          SubexpFlatCount.store,hvalue,hempty 325 (by simp),
          hempty 326 (by simp),hempty 327 (by simp),hempty 328 (by simp),hempty 329 (by simp)]
  obtain ⟨steps,b,hsteps,_,htrace,_,_,_,⟨regs,hb⟩,_⟩ :=
    ReconstructionSpace.canonical_query_run_space t ht hd model M cache x count hcount hx q
      (q.regs ∘ LeafProgram.QueryReadback.regMap) (a.stacks 194) (a.stacks 202)
      hm hw hr hs ha S hB hmodulus hinput
  change b = LeafProgram.QueryReadback.finish q regs (DisjointReuse.binaryNat count)
    (a.stacks 194) (a.stacks 202) at hb
  rw [hb] at htrace
  have he := eval_call_lifted ReconstructionSpace.canonicalQueryProgram
    LeafProgram.QueryReadback.Wide.regMap LeafProgram.QueryReadback.Wide.stackMap a
    LeafProgram.QueryReadback.Wide.regMap_injective
    LeafProgram.QueryReadback.Wide.stackMap_injective htrace
  change Eval canonicalWideRead (steps+1)
    (LeafProgram.QueryReadback.Wide.install a q)
    (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count)) at he
  rw [LeafProgram.QueryReadback.Wide.install_project] at he
  exact ⟨steps+1,regs,hsteps,he⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read_oai
