-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:19:46.040254+00:00
-- url     : https://prove2.me/submissions/a3b16b61-a90c-4f7c-825d-fec2029749e6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S126
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_budgetCall_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationCorrectness_normalizedBody_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Asymptotics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical parameters for the disjoint counting reduction. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem sparsifyNu_pos {n : ℕ} (hn : 20 ≤ n) : 0 < sparsifyNu n := by
  have hLambda : 2 ≤ sparsifyLambda n := by
    have h := (Nat.pow_lt_iff_lt_clog (by norm_num : 1 < (2 : ℕ))).mp
      (show 2 ^ 1 < n by omega)
    exact h
  exact Nat.clog_pos (by norm_num) hLambda

theorem sparsifySchedule_le_lambda (n : ℕ) : sparsifySchedule n ≤ sparsifyLambda n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem sparsify_parameters_le_input (n : ℕ) :
    sparsifyLambda n ≤ n ∧ sparsifyNu n ≤ n ∧ sparsifySchedule n ≤ n := by
  have hLambda : sparsifyLambda n ≤ n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  have hNu : sparsifyNu n ≤ sparsifyLambda n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  exact ⟨hLambda, hNu.trans hLambda, (sparsifySchedule_le_lambda n).trans hLambda⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.CounterPrograms

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [List.cons_append, value, List.length_cons, ih, pow_succ]
      ring

theorem value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
        List.length_cons, pow_succ] <;> omega

theorem trimTail_length_le (xs : List Bool) : (trimTail xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [trimTail]
  | cons b xs ih => cases b <;> simp [trimTail]; omega

/-- A most-significant one followed by `m` bits has binary logarithm `m`. -/
theorem log2_value_append_true (xs : List Bool) :
    Nat.log2 (value (xs ++ [true])) = xs.length := by
  have hbound := value_lt_two_pow_length xs
  have hpow : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  have hval : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
    simp [value_append, value]
  have hpos : value (xs ++ [true]) ≠ 0 := by omega
  apply Nat.le_antisymm
  · have hlt : value (xs ++ [true]) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]
      omega
    have h := (Nat.log2_lt hpos).mpr hlt
    omega
  · exact (Nat.le_log2 hpos).mpr (by omega)

theorem trimTail_reverse_length (xs : List Bool) :
    (trimTail xs.reverse).length = Nat.log2 (value xs) := by
  induction xs using List.reverseRecOn with
  | nil => simp [trimTail, value]
  | append_singleton xs b ih =>
      cases b with
      | false => simpa [List.reverse_append, trimTail, value_append, value] using ih
      | true => simp [List.reverse_append, trimTail, log2_value_append_true]

theorem atoms_eval {r s : ℕ} (ops : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (atoms ops) ops.length d (runAtoms ops d) := by
  induction ops generalizing d with
  | nil => exact .skip d
  | cons op ops ih =>
      simpa only [atoms, runAtoms, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom op d) (ih (op.eval d))

theorem trim_finish (b present : Bool) (xs : List Bool) :
    Trace trimProgram 3 (trimCfg (some 3) b present xs) (trimCfg none false false xs) := by
  refine .cons (b := trimCfg (some 4) false present xs) ?_
    (.cons (b := trimCfg (some 5) false false xs) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, trimProgram, trimCfg, execInstr]

theorem trim_trace (xs : List Bool) (b present : Bool) :
    Trace trimProgram (trimCost xs) (trimCfg (some 0) b present xs)
      (trimCfg none false false (trimTail xs)) := by
  induction xs generalizing b present with
  | nil =>
      refine .cons (b := trimCfg (some 1) false false []) ?_
        (.cons ?_ (trim_finish false false []))
      all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]
  | cons a xs ih =>
      cases a with
      | false =>
          refine .cons (b := trimCfg (some 1) false true xs) ?_
            (.cons (b := trimCfg (some 2) false true xs) ?_
              (.cons ?_ (ih false true)))
          all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]
      | true =>
          refine .cons (b := trimCfg (some 1) true true xs) ?_
            (.cons (b := trimCfg (some 2) true true xs) ?_
              (.cons ?_ (trim_finish true true xs)))
          all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]

theorem trimCost_le (xs : List Bool) : trimCost xs ≤ 3 * xs.length + 6 := by
  induction xs with
  | nil => simp [trimCost]
  | cons a xs ih => cases a <;> simp only [trimCost, List.length_cons] <;> omega

theorem trim_complete_trace (xs : List Bool) :
    Trace trimProgram (trimCost xs) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) := by
  have hi : initial trimProgram xs = trimCfg (some 0) false false xs := by
    simp [initial, trimProgram, trimCfg]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  have ht : terminal trimProgram (trimTail xs) = trimCfg none false false (trimTail xs) := by
    simp [terminal, trimProgram, trimCfg]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  rw [hi, ht]
  exact trim_trace xs false false

theorem trim_complete_runs (xs : List Bool) :
    RunsIn trimProgram (3 * xs.length + 6) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) :=
  ⟨trimCost xs, trimCost_le xs, trim_complete_trace xs⟩

/-! ## Concrete input reversal -/

theorem reverseTransfer_trace (xs : List Bool) :
    Trace reverseTransfer (3 * xs.length + 3) (initial reverseTransfer xs)
      (terminal reverseTransfer xs.reverse) := by
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 3)
    0 1 0 1 (by decide) (by decide) (fun _ => false)
    (fun i => if i = 0 then xs else [])
  have ht : StackRoutines.transferResult (3 : Fin 4) (0 : Fin 3) 1 (0 : Fin 3) 1
      (fun _ => false) (fun i => if i = 0 then xs else []) =
      {terminal reverseTransfer xs.reverse with pc := some 3} := by
    simp [StackRoutines.transferResult, StackRoutines.transferStacks,
      reverseTransfer, StackRoutines.transferProgram, readRegs]
    first | done | (funext i; fin_cases i <;> simp)
  have hh : Trace reverseTransfer 1
      {terminal reverseTransfer xs.reverse with pc := some 3}
      (terminal reverseTransfer xs.reverse) := by
    refine .cons ?_ (.refl _)
    simp [step, reverseTransfer, StackRoutines.transferProgram, execInstr, terminal]
  rw [ht] at h
  change Trace reverseTransfer (3 * xs.length + 2) (initial reverseTransfer xs)
    {terminal reverseTransfer xs.reverse with pc := some 3} at h
  exact h.trans hh

theorem enter_terminal_eq_initial {r s l m : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (word : List Bool) :
    ProgramLinking.enter q (terminal p word) = initial q word := by
  simp [ProgramLinking.enter, initial, h]

theorem link_io_runs {r s l m n₁ n₂ : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (input middle output : List Bool)
    (hp : RunsIn p n₁ (initial p input) (terminal p middle))
    (hq : RunsIn q n₂ (initial q middle) (terminal q output)) :
    RunsIn (ProgramLinking.link p q) (n₁ + n₂)
      (initial (ProgramLinking.link p q) input)
      (terminal (ProgramLinking.link p q) output) := by
  exact ProgramLinking.link_complete_runsIn p q input output hp rfl
    (by simpa only [enter_terminal_eq_initial p q h middle] using hq)

theorem prepareLog_runs (xs : List Bool) :
    RunsIn prepareLogProgram (6 * xs.length + 9)
      (initial prepareLogProgram xs)
      (terminal prepareLogProgram (trimTail xs.reverse)) := by
  have h := link_io_runs reverseTransfer trimProgram rfl xs xs.reverse
    (trimTail xs.reverse) ⟨_, le_rfl, reverseTransfer_trace xs⟩
    (trim_complete_runs xs.reverse)
  change RunsIn (ProgramLinking.link reverseTransfer trimProgram) (6 * xs.length + 9)
    (initial (ProgramLinking.link reverseTransfer trimProgram) xs)
    (terminal (ProgramLinking.link reverseTransfer trimProgram) (trimTail xs.reverse))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [List.length_reverse]
  omega

/-! ## Reindex and call the checked binary word-length counter -/

theorem extend_equiv {α β γ : Type*} (e : α ≃ β) (f : α → γ) (frame : β → γ) :
    Function.extend e f frame = fun b => f (e.symm b) := by
  funext b
  simp

theorem lift_equiv_initial {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (initial p word) =
      initial (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, initial,
    extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

theorem lift_equiv_terminal {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (terminal p word) =
      terminal (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, terminal,
    extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

theorem swappedLength_correct (xs : List Bool) :
    ∃ output, value output = xs.length ∧ output.length ≤ xs.length ∧
      RunsIn swappedLengthProgram (xs.length * (8 * xs.length + 10) + 3)
        (initial swappedLengthProgram xs) (terminal swappedLengthProgram output) := by
  obtain ⟨output, hvalue, hlen, hrun⟩ := length_correct xs
  have h := ProgramLinking.liftProgram_runsIn lengthProgram id swapStacks
    (initial swappedLengthProgram []) Function.injective_id swapStacks.injective hrun
  refine ⟨output, hvalue, hlen, ?_⟩
  simpa only [swappedLengthProgram, lift_equiv_initial, lift_equiv_terminal] using h

theorem logBound_eq (L : ℕ) : logBound L = 8 * L ^ 2 + 16 * L + 12 := by
  unfold logBound
  ring

/-- Actual fixed-table logarithm program, correct for arbitrary padded words. -/
theorem log_correct (xs : List Bool) :
    ∃ output, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      RunsIn logProgram (logBound xs.length)
        (initial logProgram xs) (terminal logProgram output) := by
  obtain ⟨output, hvalue, hlen, hcount⟩ := swappedLength_correct (trimTail xs.reverse)
  have hrun := link_io_runs prepareLogProgram swappedLengthProgram rfl
    xs (trimTail xs.reverse) output (prepareLog_runs xs) hcount
  have htail : (trimTail xs.reverse).length ≤ xs.length := by
    simpa using trimTail_length_le xs.reverse
  refine ⟨output, hvalue.trans (trimTail_reverse_length xs), hlen.trans htail, hrun.mono ?_⟩
  have hmul := Nat.mul_le_mul htail
    (show 8 * (trimTail xs.reverse).length + 10 ≤ 8 * xs.length + 10 by omega)
  dsimp [logBound]
  nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

theorem incrementPorts_injective : Function.Injective incrementPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [incrementPorts]

theorem increment_eval (xs : List Bool) :
    Eval increment (CounterPrograms.rippleCost true xs + 1) (io xs) (io (ripple true xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) id incrementPorts
    (io xs) Function.injective_id incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple true xs))
    (CounterPrograms.ripple_terminal_trace true xs)
  have ha : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs)) = io (ripple true xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [incrementPorts, io, StructuredProgram.ioState,
        Fin.exists_fin_succ]
  change Eval increment _ (embedState id incrementPorts (io xs)
    (StructuredProgram.ioState (0 : Fin 2) xs))
    (embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs))) at he
  simpa only [increment, ha, hb] using he

theorem logarithm_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      t ≤ Floor.logBound xs.length ∧
      Eval logarithm t (io xs) (io output) := by
  obtain ⟨output, hv, hl, t, ht, he⟩ := Floor.log_correct xs
  exact ⟨output, t, hv, hl, ht, .call _ he⟩

theorem logSucc_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) + 1 ∧ output.length ≤ xs.length + 1 ∧
      t ≤ 32 * (xs.length + 1)^2 ∧ Eval logSucc t (io xs) (io output) := by
  obtain ⟨ys, t, hv, hl, ht, he⟩ := logarithm_eval xs
  refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
    he.seq (increment_eval ys)⟩
  · rw [CounterPrograms.value_increment, hv]
  · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
  · have hc := CounterPrograms.rippleCost_le true ys
    rw [Floor.logBound_eq] at ht
    nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

theorem decrement_eval (xs : List Bool) :
    Eval decrement (CounterPrograms.rippleCost false xs + 1)
      (io xs) (io (ripple false xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram false) id
    Setup.incrementPorts (io xs) Function.injective_id Setup.incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple false xs))
    (CounterPrograms.ripple_terminal_trace false xs)
  have ha : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple false xs)) = io (ripple false xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [Setup.incrementPorts, io, Setup.io,
        StructuredProgram.ioState, Fin.exists_fin_succ]
  simpa only [decrement, ha, hb] using he

theorem reset_eval (d : Data) : Eval reset 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := Floor.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  convert Eval.base h using 1
  · rfl
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl

theorem clog_eq_log_pred (t : ℕ) (ht : 2 ≤ t) :
    Nat.clog 2 t = Nat.log2 (t-1) + 1 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_antisymm
  · apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (t-1)
    omega
  · have hp := Nat.pow_log_le_self 2 (show t-1 ≠ 0 by omega)
    have hlt : 2 ^ Nat.log 2 (t-1) < t := by omega
    have hh := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hlt
    omega

private theorem zero_branch_cost_le (r L : ℕ) (hr : r ≤ 8 * L + 7) :
    (r + 1) + ((8 * L + 6) + (3 + 1)) ≤ 64 * (L + 2) ^ 2 := by
  nlinarith

private theorem nonzero_branch_cost_le (r t L : ℕ) (hr : r ≤ 8 * L + 7)
    (ht : t ≤ 32 * (L + 1) ^ 2) :
    (r + 1) + ((8 * L + 6) + ((3 + t) + 1)) ≤ 64 * (L + 2) ^ 2 := by
  nlinarith

theorem command_eval (xs : List Bool) (hx : 0 < value xs) :
    ∃ output n, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length + 1 ∧ n ≤ 64*(xs.length+2)^2 ∧
      Eval command n (io xs) (io output) := by
  let ys := ripple false xs
  let z := CounterForPrograms.zeroResult zeroPorts (io ys)
  have hy : value ys = value xs - 1 := by
    have h := CounterPrograms.value_decrement hx
    dsimp [ys]
    omega
  have hlen : ys.length = xs.length := CounterPrograms.decrement_length hx
  have hz := CounterForPrograms.zero_eval zeroPorts (io ys) (by rfl)
  have hzs : z.stacks = (io ys).stacks := by
    exact CounterForPrograms.install_stacks_self zeroPorts (io ys) _ _ _ rfl
  have hzf : z.regs 2 = CounterPrograms.isZero ys := by
    exact CounterForPrograms.install_register zeroPorts (io ys) _ _ _ _ _ 2
  have hr : Eval reset 3 z (io ys) := by
    simpa only [hzs] using reset_eval z
  have hc := CounterPrograms.rippleCost_le false xs
  by_cases hzero : value ys = 0
  · have ht : value xs = 1 := by omega
    have hb : z.regs 2 = true := hzf.trans ((CounterPrograms.isZero_eq_true_iff ys).mpr hzero)
    refine ⟨ys, (CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+(3+1)), ?_, ?_, ?_, ?_⟩
    · simp [hzero, ht]
    · omega
    · rw [hlen]
      exact zero_branch_cost_le _ _ hc
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_true hb hr))
  · obtain ⟨out,n,hv,hl,hn,he⟩ := Setup.logSucc_eval ys
    have hb : z.regs 2 = false := hzf.trans
      ((CounterPrograms.isZero_eq_false_iff ys).mpr (by omega))
    refine ⟨out,(CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+((3+n)+1)), ?_, ?_, ?_, ?_⟩
    · rw [hv, hy, clog_eq_log_pred _ (by omega)]
    · omega
    · rw [hlen] at hn ⊢
      exact nonzero_branch_cost_le _ _ _ hc hn
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_false hb (hr.seq he)))

theorem program_runs (xs : List Bool) (hx : 0 < value xs) :
    ∃ output, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length+1 ∧
      RunsIn program (65*(xs.length+2)^2)
        (initial program xs) (terminal program output) := by
  obtain ⟨out,n,hv,hl,hn,he⟩ := command_eval xs hx
  exact ⟨out,hv,hl,n+1,by nlinarith,compiled_io_trace 0 0 he⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

open SparseCharging

theorem chooseExponent_le (k a b e : ℕ) (ha : 0 < a)
    (he : parameterTest k a b e = true) : chooseExponent k a b ha ≤ e :=
  Nat.find_min' (exists_parameter k a b ha) he

/-- The first successful candidate inherits the sharp witness bound. Constants
are chosen before the rational budget numerator and denominator. -/
theorem choose_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a),
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 (inverseIndex a b) + 1) := by
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  let q := k - 2
  let T := 2 * (rightConstant k * (A + 2 + 4 * (q + 1) + 1) + 1)
  refine ⟨4 * 2 ^ T, T, ?_⟩
  intro a b ha
  let s := inverseIndex a b
  obtain ⟨T', e, _, hγ, hM, hbudget, hsize, hindex, hT⟩ :=
    dyadic_witness (depthConstant k) A q (rightConstant k) s
      (by exact Nat.zero_lt_succ _) (fun M hM => depthConstant_le k M hM)
  have he : parameterTest k a b e = true := by
    simp only [parameterTest, decide_eq_true_eq]
    refine ⟨hM, hγ, ?_⟩
    calc
      rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
          rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
        Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
      _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
      _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget
  have hmin := chooseExponent_le k a b e ha he
  have hT' : T' = T := hT
  subst T'
  exact ⟨(Nat.pow_le_pow_right (by decide) hmin).trans hsize, hmin.trans hindex⟩

theorem inverseIndex_le_denominator (a b : ℕ) (hb : 0 < b) : inverseIndex a b ≤ b := by
  have := Nat.div_le_self (b - 1) a
  dsimp [inverseIndex]
  omega

/-- Search length is logarithmic in the positive rational denominator; candidate
values remain polynomial in it. This exposes the uniform parameter-size budget. -/
theorem choose_encoding_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a), 0 < b →
      chooseM k a b ha ≤ K * b ^ 2 ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 b + 1) := by
  obtain ⟨K, T, h⟩ := choose_bounds k
  refine ⟨K, T, ?_⟩
  intro a b ha hb
  have hs := inverseIndex_le_denominator a b hb
  have hlog : Nat.log 2 (inverseIndex a b) + 1 ≤ inverseIndex a b :=
    Nat.succ_le_of_lt (Nat.log_lt_self 2 (by exact Nat.succ_ne_zero _))
  constructor
  · calc
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) :=
        (h a b ha).1
      _ ≤ K * b * b := Nat.mul_le_mul (Nat.mul_le_mul_left K hs) (hlog.trans hs)
      _ = K * b ^ 2 := by ring
  · exact (h a b ha).2.trans (by have := Nat.log_mono_right (b := 2) hs; omega)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Concrete finite-control construction of the Appendix A dyadic search.
The input budget is `1 / s`; the search uses only exact binary arithmetic.
This file separates command construction from theorems about its execution.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram

open BitProgram StructuredCalls BinaryArithmetic
open ParametersProgram
open scoped BigOperators

theorem chooseExponent_input_bits (k : ℕ) :
    ∃ T : ℕ, ∀ s : List Bool, 0 < toNat s →
      SparseBudget.chooseExponent k 1 (toNat s) (by decide) ≤ T + 2 * s.length := by
  obtain ⟨K, T, h⟩ := SparseBudget.choose_encoding_bounds k
  refine ⟨T, ?_⟩
  intro s hs
  have hb := ModularArithmetic.toNat_lt_pow_length s
  have hl := Nat.log_lt_of_lt_pow (ne_of_gt hs) hb
  have hn := (h 1 (toNat s) (by decide) hs).2
  omega

/-- Constants are chosen before the binary input. This is polynomial in encoding
length, not in the integer represented by the input word. -/
theorem searchCost_polynomial (k : ℕ) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s → searchCost k s ≤ K * (s.length + 1) ^ 3 := by
  obtain ⟨T, hT⟩ := chooseExponent_input_bits k
  let g := (SparseCharging.rightConstant k).bits.length
  let D := (k + 2) * (T + g + 32)
  let E := 12000 * (k + 1) * D ^ 2 + 2 * g + 21
  refine ⟨(T + 5) * E, ?_⟩
  intro s hs
  let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
  have hN : N ≤ T + 2 * s.length := hT s hs
  have hN' : N + 3 ≤ (T + 5) * (s.length + 1) := by nlinarith
  have hwidth : candidateWidth k s (dyadicWord N) ≤ D * (s.length + 1) := by
    simp only [candidateWidth, dyadicWord_length]
    have hsub := Nat.mul_le_mul_right (N + 1 + 6) (Nat.sub_le k 1)
    have hscaled := Nat.mul_le_mul_left (k + 1) hN
    have hD₁ : 2 * k + 3 ≤ D := by dsimp [D]; nlinarith
    have hD₂ : (k + 1) * T + 7 * k + g + 21 ≤ D := by dsimp [D]; nlinarith
    have hD₃ := Nat.mul_le_mul_right s.length hD₁
    change _ ≤ D * (s.length + 1)
    change _ + _ + _ + g + _ ≤ _
    nlinarith
  have hsq := Nat.pow_le_pow_left hwidth 2
  have hone : 1 ≤ (s.length + 1) ^ 2 := by nlinarith
  have hconstant := Nat.mul_le_mul_left (2 * g + 21) hone
  have hterm : 12000 * (k + 1) * candidateWidth k s (dyadicWord N) ^ 2 + 2 * g + 21 ≤
      E * (s.length + 1) ^ 2 := by
    dsimp [E]
    rw [mul_pow] at hsq
    have hscaled := Nat.mul_le_mul_left (12000 * (k + 1)) hsq
    nlinarith
  have hprod := Nat.mul_le_mul hN' hterm
  dsimp [searchCost]
  change (N + 3) * _ ≤ _
  calc
    _ ≤ ((T + 5) * (s.length + 1)) * (E * (s.length + 1) ^ 2) := hprod
    _ = (T + 5) * E * (s.length + 1) ^ 3 := by ring

theorem commandCost_polynomial (k : ℕ) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s → commandCost k s ≤ K * (s.length + 1) ^ 3 := by
  obtain ⟨K, hK⟩ := searchCost_polynomial k
  obtain ⟨T, hT⟩ := chooseExponent_input_bits k
  let D := 5 + k * (T + 4)
  let g := (SparseCharging.rightConstant k).bits.length
  refine ⟨K + 600 * k * D ^ 2 + 2 * g + 50, ?_⟩
  intro s hs
  have hsearch := hK s hs
  have hindex := Nat.mul_le_mul_left k (hT s hs)
  have harg : 5 + k * (SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 2) ≤
      D * (s.length + 1) := by
    have hcoef : 2 * k ≤ D := by dsimp [D]; nlinarith
    have hconst : 5 + k * (T + 2) ≤ D := by dsimp [D]; nlinarith
    have hlin := Nat.mul_le_mul_right s.length hcoef
    calc
      _ ≤ (5 + k * (T + 2)) + 2 * k * s.length := by nlinarith
      _ ≤ D + D * s.length := Nat.add_le_add hconst hlin
      _ = D * (s.length + 1) := by ring
  have hsquare := Nat.pow_le_pow_left harg 2
  rw [mul_pow] at hsquare
  have hscaled := Nat.mul_le_mul_left (600 * k) hsquare
  have hpow : (s.length + 1) ^ 2 ≤ (s.length + 1) ^ 3 := by
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hone : 1 ≤ (s.length + 1) ^ 3 := Nat.one_le_pow' 3 s.length
  have hp := Nat.mul_le_mul_left (600 * k * D ^ 2) hpow
  have hc := Nat.mul_le_mul_left (2 * g + 50) hone
  dsimp [commandCost]
  change _ + _ + 2 * g + 50 ≤ _
  nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem clearSequence_eval (ports : List (Fin 1220)) (a : State 80 1220) (B : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ (2 * B + 3) * ports.length ∧
      Eval (clearSequence ports) steps a b ∧
      (∀ i ∈ ports, b.stacks i = []) ∧
      (∀ i, i ∉ ports → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  induction ports generalizing a with
  | nil => exact ⟨0, a, by simp, .base (.skip a), by simp, by simp, hbound⟩
  | cons port rest ih =>
    have hlocal : ∀ i, ((clearOutputState port a).stacks i).length ≤ B := by
      intro i
      by_cases hi : i = port
      · subst i; simp [clearOutputState]
      · simpa [clearOutputState, hi] using hbound i
    obtain ⟨steps, b, hs, he, hc, hf, hb⟩ := ih (clearOutputState port a) hlocal
    refine ⟨2 * (a.stacks port).length + 3 + steps, b, ?_,
      (clearOutput_eval port a).seq he, ?_, ?_, hb⟩
    · have := hbound port
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with hip | hi
      · subst i
        by_cases hp : port ∈ rest
        · exact hc port hp
        · rw [hf port hp]; simp [clearOutputState]
      · exact hc i hi
    · intro i hi
      have hip : i ≠ port := fun h => hi (List.mem_cons.mpr (.inl h))
      have hir : i ∉ rest := fun h => hi (List.mem_cons.mpr (.inr h))
      rw [hf i hir]
      simp [clearOutputState, hip]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ScheduleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary construction of the disjoint-sparsification parameter.
All arithmetic uses fixed finite programs; the input numeral is runtime stack data. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

theorem reset_eval (d : Data) : Eval reset 3 d ⟨resetRegs d.regs, d.stacks⟩ := by
  exact .base (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))

theorem clogStacks_injective (port : Fin 32) (h6 : port ≠ 6) (h7 : port ≠ 7) :
    Function.Injective (clogStacks port) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clogStacks]

/-- The two work stacks are restored, and all other caller stacks are framed. -/
theorem clogAt_eval (port : Fin 32) (h6 : port ≠ 6) (h7 : port ≠ 7)
    (d : Data) (hwork6 : d.stacks 6 = []) (hwork7 : d.stacks 7 = [])
    (hpos : 0 < toNat (d.stacks port)) :
    ∃ t word,
      Eval (clogAt port) t d ⟨resetRegs d.regs, Function.update d.stacks port word⟩ ∧
      toNat word = Nat.clog 2 (toNat (d.stacks port)) ∧
      word.length ≤ (d.stacks port).length + 1 ∧
      t ≤ 68 * ((d.stacks port).length + 2) ^ 2 := by
  obtain ⟨word, hv, hl, t, ht, htrace⟩ :=
    DisjointReuse.BinaryClogProgram.program_runs (d.stacks port)
      (by simpa only [CounterPrograms.value_eq_toNat] using hpos)
  let a : Data := ⟨resetRegs d.regs, d.stacks⟩
  have he (xs : List Bool) :
      embedState (Fin.castAdd 5) (clogStacks port) a (StructuredProgram.ioState 0 xs) =
        (⟨resetRegs d.regs, Function.update d.stacks port xs⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 3 5)
      (clogStacks_injective port h6 h7)
    · intro i
      fin_cases i <;> simp [resetRegs]
    · intro i hi
      rfl
    · intro i
      fin_cases i <;> simp [clogStacks, h6.symm, h7.symm,
        hwork6, hwork7]
    · intro i hi
      have hn : i ≠ port := fun h => hi ⟨0, h.symm⟩
      simp [a, hn]
  have hc := eval_call_lifted DisjointReuse.BinaryClogProgram.program
    (Fin.castAdd 5) (clogStacks port) a (Fin.castAdd_injective 3 5)
    (clogStacks_injective port h6 h7)
    (a := StructuredProgram.ioState 0 (d.stacks port))
    (b := StructuredProgram.ioState 0 word) htrace
  change Eval _ t
    (embedState (Fin.castAdd 5) (clogStacks port) a
      (StructuredProgram.ioState 0 (d.stacks port)))
    (embedState (Fin.castAdd 5) (clogStacks port) a
      (StructuredProgram.ioState 0 word)) at hc
  rw [he, he, Function.update_eq_self] at hc
  refine ⟨3 + t, word, (reset_eval d).seq hc, ?_, hl, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hv
  · have hp : 1 ≤ ((d.stacks port).length + 2) ^ 2 := by
      simpa using Nat.pow_le_pow_left (show 1 ≤ (d.stacks port).length + 2 by omega) 2
    omega

theorem slots_update (words : Fin 6 → List Bool) (i : Fin 6) (word : List Bool) :
    Function.update (slots words) (Fin.castAdd 26 i) word =
      slots (Function.update words i word) := by
  funext j
  by_cases hj : j.val < 6
  · let k : Fin 6 := ⟨j.val, hj⟩
    have heq : j = Fin.castAdd 26 k := Fin.ext rfl
    conv_lhs => rw [heq]
    conv_rhs => rw [heq]
    simp only [Function.update_apply, slots_low, (Fin.castAdd_injective 6 26).eq_iff]
  · have hne : j ≠ Fin.castAdd 26 i := by
      intro h
      have hv := congrArg Fin.val h
      have := i.isLt
      simp only [Fin.val_castAdd] at hv
      omega
    simp [slots, hj, Function.update_of_ne hne]

theorem initialData_eq (input : List Bool) :
    initialData input = StructuredProgram.ioState 0 input := by
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [initialData, slots, Fin.coe_ofNat_eq_mod, initialWords]

/-- Exact parameter construction. The returned words are physically retained on
ports1..5; all local scratch stacks are empty, and the original binary n survives. -/
theorem command_eval (input : List Bool) (hn : 20 ≤ toNat input) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval command t (initialData input) ⟨rf, slots words⟩ ∧
      words 0 = input ∧
      toNat (words 1) = sparsifyLambda (toNat input) ∧
      toNat (words 2) = sparsifyNu (toNat input) ∧
      toNat (words 3) = sparsifyNu (toNat input) ^ 2 ∧
      toNat (words 4) = Nat.sqrt (sparsifyLambda (toNat input)) ∧
      toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      t ≤ 10000000 * (toNat input + input.length + 6) ^ 3 := by
  let w0 := initialWords input
  let d0 := initialData input
  have hc1 := ArithmeticCalls.copyAt_eval (0 : Fin 32) 1 6 d0
    (by decide) (by decide) (by decide) (by rfl) (by rfl)
  let d1 := ArithmeticCalls.afterCopy 0 1 d0
  obtain ⟨t1, lambda, hl1, hv1, hlen1, ht1⟩ := clogAt_eval 1 (by decide) (by decide) d1
    (by simp [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod])
    (by simp [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod])
    (by simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using
      (show 0 < toNat input by omega))
  let w1 := Function.update w0 1 lambda
  let r1 := resetRegs d1.regs
  let d2 : Data := ⟨r1, slots w1⟩
  have hd2 : (⟨resetRegs d1.regs, Function.update d1.stacks 1 lambda⟩ : Data) = d2 := by
    apply CounterForPrograms.data_ext
    · rfl
    · simp only [d1, ArithmeticCalls.afterCopy, d0, initialData, Function.update_idem]
      exact slots_update w0 1 lambda
  rw [hd2] at hl1
  have hv1' : toNat lambda = sparsifyLambda (toNat input) := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords,
      sparsifyLambda] using hv1
  have hlen1' : lambda.length ≤ input.length + 1 := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using hlen1
  have ht1' : t1 ≤ 68 * (input.length + 2) ^ 2 := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using ht1
  have hc2 := ArithmeticCalls.copyAt_eval (1 : Fin 32) 2 6 d2
    (by decide) (by decide) (by decide)
    (by simp [d2, slots, Fin.coe_ofNat_eq_mod, w1, w0, initialWords])
    (by simp [d2, slots, Fin.coe_ofNat_eq_mod])
  let d3 := ArithmeticCalls.afterCopy 1 2 d2
  obtain ⟨t2, nu, hl2, hv2, hlen2, ht2⟩ := clogAt_eval 2 (by decide) (by decide) d3
    (by simp [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod])
    (by simp [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod])
    (by
      have hpos : 0 < sparsifyLambda (toNat input) := Nat.clog_pos (by decide) (by omega)
      simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1, hv1'] using hpos)
  let w2 := Function.update w1 2 nu
  let r2 := resetRegs d3.regs
  let d4 : Data := ⟨r2, slots w2⟩
  have hd4 : (⟨resetRegs d3.regs, Function.update d3.stacks 2 nu⟩ : Data) = d4 := by
    apply CounterForPrograms.data_ext
    · rfl
    · simp only [d3, ArithmeticCalls.afterCopy, d2, Function.update_idem]
      exact slots_update w1 2 nu
  rw [hd4] at hl2
  have hv2' : toNat nu = sparsifyNu (toNat input) := by
    simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1, hv1', sparsifyNu] using hv2
  have hlen2' : nu.length ≤ input.length + 2 := by
    have : nu.length ≤ lambda.length + 1 := by
      simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1] using hlen2
    omega
  have ht2' : t2 ≤ 68 * (lambda.length + 2) ^ 2 := by
    simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1] using ht2
  obtain ⟨tm, rm, square, hm, hvm, hlenm, htm⟩ := ArithmeticCalls.multiplyAt_eval squarePorts d4
    ⟨by simp [d4, slots, Fin.coe_ofNat_eq_mod, w2, w1, w0, initialWords, squarePorts],
      by intro i; simp [d4, squarePorts]⟩
  let w3 := Function.update w2 3 square
  let d5 : Data := ⟨rm, slots w3⟩
  have hd5 : (⟨rm, Function.update d4.stacks squarePorts.out square⟩ : Data) = d5 := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w2 3 square
  rw [hd5] at hm
  have hvm' : toNat square = sparsifyNu (toNat input) ^ 2 := by
    simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2, hv2', pow_two] using hvm
  have hlenm' : square.length ≤ 2 * input.length + 5 := by
    have : square.length ≤ nu.length + nu.length + 1 := by
      simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2] using hlenm
    omega
  have htm' : tm ≤ 100 * (nu.length + nu.length + 1) ^ 2 := by
    simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2] using htm
  obtain ⟨tr, rr, root, hr, hvr, hlenr, htr⟩ :=
    SqrtLog.LeafParameterArithmetic.sqrtAt_eval sqrtPorts d5
      ⟨by simp [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, w0, initialWords],
        by intro i; simp [d5, sqrtPorts]⟩
  let w4 := Function.update w3 4 root
  let d6 : Data := ⟨rr, slots w4⟩
  have hd6 : (⟨rr, Function.update d5.stacks sqrtPorts.out root⟩ : Data) = d6 := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w3 4 root
  rw [hd6] at hr
  have hvr' : toNat root = Nat.sqrt (sparsifyLambda (toNat input)) := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using hvr
  have hlenr' : root.length ≤ sparsifyLambda (toNat input) := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using hlenr
  have htr' : tr ≤ 200001 * (sparsifyLambda (toNat input) + lambda.length + 2) ^ 3 := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using htr
  obtain ⟨tq, rq, result, hq, hvq, hlenq, htq⟩ :=
    SqrtLog.LeafParameterArithmetic.quotientAt_eval quotientPorts d6
      ⟨by simp [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, w2, w1, w0, initialWords],
        by intro i; simp [d6, quotientPorts]⟩
      (by simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, hvm'] using
        (pow_pos (sparsifyNu_pos hn) 2))
  let w5 := Function.update w4 5 result
  have hd7 : (⟨rq, Function.update d6.stacks quotientPorts.out result⟩ : Data) =
      ⟨rq, slots w5⟩ := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w4 5 result
  rw [hd7] at hq
  have hvq' : toNat result = sparsifySchedule (toNat input) := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, hvr', hvm', sparsifySchedule] using hvq
  have hlenq' : result.length = root.length := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4] using hlenq
  have htq' : tq ≤ 150 * (root.length + square.length + 1) ^ 2 := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3] using htq
  refine ⟨(7 * input.length + 5) + (t1 + ((7 * lambda.length + 5) +
    (t2 + (tm + (tr + tq))))), rq, w5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := hc1.seq (hl1.seq (hc2.seq (hl2.seq (hm.seq (hr.seq hq)))))
    simpa [command, d0, initialData, d2, slots, Fin.coe_ofNat_eq_mod, w1, w0, initialWords] using he
  · simp [w5, w4, w3, w2, w1, w0, initialWords]
  · simpa [w5, w4, w3, w2, w1] using hv1'
  · simpa [w5, w4, w3, w2] using hv2'
  · simpa [w5, w4, w3] using hvm'
  · simpa [w5, w4] using hvr'
  · simpa [w5] using hvq'
  · simpa [w5, hlenq'] using hlenr'
  · have hLambda : sparsifyLambda (toNat input) ≤ toNat input :=
      (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp (Nat.lt_two_pow_self.le)
    let X := toNat input + input.length + 6
    have hX : 1 ≤ X := by dsimp [X]; omega
    have hsq : X ^ 2 ≤ X ^ 3 := by
      calc
        X ^ 2 = X ^ 2 * 1 := by simp
        _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX
        _ = X ^ 3 := by ring
    have hp1 := Nat.pow_le_pow_left (show input.length + 2 ≤ X by dsimp [X]; omega) 2
    have hp2 := Nat.pow_le_pow_left (show lambda.length + 2 ≤ X by dsimp [X]; omega) 2
    have hpm := Nat.pow_le_pow_left (show nu.length + nu.length + 1 ≤ 2 * X by
      dsimp [X]; omega) 2
    have hpr := Nat.pow_le_pow_left
      (show sparsifyLambda (toNat input) + lambda.length + 2 ≤ X by dsimp [X]; omega) 3
    have hpq := Nat.pow_le_pow_left (show root.length + square.length + 1 ≤ 2 * X by
      dsimp [X]; omega) 2
    have hlX : input.length ≤ X := by dsimp [X]; omega
    have hl1X : lambda.length ≤ X := by dsimp [X]; omega
    change _ ≤ 10000000 * X ^ 3
    nlinarith only [ht1', ht2', htm', htr', htq', hp1, hp2, hpm, hpr, hpq, hsq,
      hX, hlX, hl1X]


/-- The compiled local schedule has one actual trace and a uniform all-port,
every-prefix bound. The polynomial depends on n and the retained binary width. -/
theorem program_trace (input : List Bool) (hn : 20 ≤ toNat input) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Trace program steps (initial program input) ((⟨rf, slots words⟩ : Data).withPC none) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000001 * (toNat input + input.length + 6) ^ 3 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps → Trace program prefixSteps (initial program input)
        intermediate → ∀ i,
        (intermediate.stacks i).length ≤
          input.length + 10000001 * (toNat input + input.length + 6) ^ 3 := by
  obtain ⟨t, rf, words, he, h0, _, _, _, _, h5, hlen, ht⟩ := command_eval input hn
  have htrace := compiled_halt_trace he (0 : Fin 32) 5
  rw [initialData_eq] at htrace
  change Trace program (t + 1) (initial program input)
    ((⟨rf, slots words⟩ : Data).withPC none) at htrace
  have htime : t + 1 ≤ 10000001 * (toNat input + input.length + 6) ^ 3 := by
    have hp : 1 ≤ (toNat input + input.length + 6) ^ 3 := by
      simpa using Nat.pow_le_pow_left
        (show 1 ≤ toNat input + input.length + 6 by omega) 3
    omega
  refine ⟨t + 1, rf, words, htrace, h0, h5, hlen, htime, ?_⟩
  intro prefixSteps intermediate hprefix hp i
  have hlocal := StructuredSpace.local_stack_bound program
    (steps := 10000001 * (toNat input + input.length + 6) ^ 3)
    (show dataBits (initial program input) ≤ input.length by simp)
  exact hlocal prefixSteps intermediate (hprefix.trans htime) hp i

theorem sharedStacks_other (i : Fin 32) (h0 : i ≠ 0) (h5 : i ≠ 5) :
    sharedStacks i = Fin.castAdd 1188 i := by
  have hzero : Fin.castAdd 1188 i ≠ (0 : Fin 1220) := by
    intro h
    apply h0
    have hv := congrArg (fun x : Fin 1220 => x.val) h
    exact Fin.ext hv
  have hfive : Fin.castAdd 1188 i ≠ (5 : Fin 1220) := by
    intro h
    apply h5
    have hv := congrArg (fun x : Fin 1220 => x.val) h
    exact Fin.ext hv
  have h267 : Fin.castAdd 1188 i ≠ (267 : Fin 1220) := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt; change i.val = 267 at hv; omega
  have h266 : Fin.castAdd 1188 i ≠ (266 : Fin 1220) := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt; change i.val = 266 at hv; omega
  change (Equiv.swap (5 : Fin 1220) 266)
    ((Equiv.swap (0 : Fin 1220) 267) (Fin.castAdd 1188 i)) = _
  rw [Equiv.swap_apply_of_ne_of_ne hzero h267, Equiv.swap_apply_of_ne_of_ne hfive h266]

theorem sharedCall_eval (input : List Bool) (hn : 20 ≤ toNat input)
    (frame : State 80 1220) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval sharedCall steps
        (embedState (Fin.castAdd 72) sharedStacks frame (StructuredProgram.ioState 0 input))
        (embedState (Fin.castAdd 72) sharedStacks frame ⟨rf, slots words⟩) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000001 * (toNat input + input.length + 6) ^ 3 := by
  obtain ⟨steps, rf, words, ht, h0, h5, hlen, htime, _⟩ := program_trace input hn
  have hcall := eval_call_lifted program (Fin.castAdd 72) sharedStacks frame
    (Fin.castAdd_injective 8 72) sharedStacks.injective
    (a := StructuredProgram.ioState 0 input) (b := ⟨rf, slots words⟩) ht
  exact ⟨steps, rf, words, hcall, h0, h5, hlen, htime⟩

private theorem resetPorts_eval (ports : List (Fin 80)) (a : State 80 1220) :
    Eval (resetPorts ports) ports.length a (resetPortsState ports a) := by
  induction ports generalizing a with
  | nil => simpa [resetPorts, resetPortsState] using (Eval.base (.skip a))
  | cons i rest ih =>
    have h := (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    convert h using 1
    · rfl
    · simp only [List.length_cons, Nat.add_comm]
    · apply CounterForPrograms.data_ext
      · funext j
        by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
          simp [resetPortsState, StructuredProgram.Atom.eval,
            StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
            execInstr, hj, hr]
      · rfl

theorem resetShared_eval (a : State 80 1220) : Eval resetShared 8 a (resetSharedState a) := by
  simpa [resetShared, resetSharedState] using
    resetPorts_eval ((List.finRange 8).map (Fin.castAdd 72)) a

theorem readySharedCall_eval (input : List Bool) (hn : 20 ≤ toNat input)
    (a : State 80 1220)
    (hports : ∀ j : Fin 32, a.stacks (sharedStacks j) =
      if j = 0 then input else []) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval readySharedCall steps a
        (embedState (Fin.castAdd 72) sharedStacks
          (resetSharedState a)
          ⟨rf, slots words⟩) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000002 * (toNat input + input.length + 6) ^ 3 := by
  let frame := resetSharedState a
  have he : embedState (Fin.castAdd 72) sharedStacks frame
      (StructuredProgram.ioState 0 input) = frame := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 72)
      sharedStacks.injective
    · intro i
      simp [frame]
    · intro i hi
      rfl
    · intro i
      exact hports i
    · intro i hi
      rfl
  obtain ⟨t, rf, words, ht, h0, h5, hlen, htime⟩ := sharedCall_eval input hn frame
  rw [he] at ht
  have hr : Eval resetShared 8 a frame := by
    exact resetShared_eval a
  refine ⟨8 + t, rf, words, hr.seq ht, h0, h5, hlen, ?_⟩
  have hcube : 8 ≤ (toNat input + input.length + 6) ^ 3 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ toNat input + input.length + 6 by omega) 3
    norm_num at h ⊢
    exact h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSetupSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

theorem budgetStacks_val (i : Fin 32) :
    (budgetStacks i).val = if i = 0 then 266 else if i = 1 then 259
      else if i = 2 then 264 else i.val := by
  fin_cases i <;> rfl

theorem scheduleStacks_val (i : Fin 32) :
    (ScheduleProgram.sharedStacks i).val =
      if i = 0 then 267 else if i = 5 then 266 else i.val := by
  fin_cases i <;> rfl

theorem scheduleStacks_off (i : Fin 1220) (hi : 32 ≤ i.val)
    (h266 : i ≠ 266) (h267 : i ≠ 267) :
    ¬ ∃ j, ScheduleProgram.sharedStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  rw [scheduleStacks_val] at hv
  split_ifs at hv with h0 h5
  · exact h267 (Fin.ext hv.symm)
  · exact h266 (Fin.ext hv.symm)
  · have := j.isLt
    omega

theorem budgetStacks_off (i : Fin 1220) (hi : 32 ≤ i.val)
    (h266 : i ≠ 266) (h259 : i ≠ 259) (h264 : i ≠ 264) :
    ¬ ∃ j, budgetStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  rw [budgetStacks_val] at hv
  split_ifs at hv with h0 h1 h2
  · exact h266 (Fin.ext hv.symm)
  · exact h259 (Fin.ext hv.symm)
  · exact h264 (Fin.ext hv.symm)
  · have := j.isLt
    omega

theorem frontendReady_stack_bound {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) (ha : FrontendReady F binary a) (hlen : binary.length ≤ n) :
    ∀ i, (a.stacks i).length ≤ Encoding.formulaBitLength F + 1 := by
  intro i
  have hn := Encoding.numVariables_le_formulaBitLength F
  by_cases hi : i = ABI.countStack
  · subst i
    rw [ha.input]
    exact Nat.le_succ _
  by_cases hu : i = 258
  · subst i
    rw [ha.header, Encoding.length_encodeNat]
    omega
  by_cases hb : i = 265
  · subst i
    rw [ha.body]
    have hl := SubexpNormalizationCorrectness.normalizedBody_length_le F
    have hh : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
      rw [Encoding.formulaBitLength_eq]
      omega
    omega
  by_cases hd : i = 267
  · subst i
    rw [ha.dimension]
    omega
  rw [ha.blank i hi hu hb hd]
  simp

theorem schedule_clear_eval (n : ℕ) (binary : List Bool) (a : State 80 1220)
    (hv : toNat binary = n) (hn : 20 ≤ n) (W : ℕ)
    (hports : ∀ j : Fin 32, a.stacks (ScheduleProgram.sharedStacks j) =
      if j = 0 then binary else [])
    (hwidth : ∀ i, (a.stacks i).length ≤ W) :
    ∃ steps b s,
      Eval (.seq ScheduleProgram.readySharedCall clearSchedule) steps a b ∧
      toNat s = sparsifySchedule n ∧ s.length ≤ n ∧
      b.stacks = Function.update a.stacks 266 s ∧
      steps ≤ 9 * 10000002 * (n + binary.length + 6) ^ 3 + 9760 * W + 20 := by
  obtain ⟨t, rf, words, hs, h0, h5, hlen5, htime⟩ :=
    ScheduleProgram.readySharedCall_eval binary (by omega) a hports
  let mid := embedState (Fin.castAdd 72) ScheduleProgram.sharedStacks
    (ScheduleProgram.resetSharedState a) ⟨rf, ScheduleProgram.slots words⟩
  change Eval ScheduleProgram.readySharedCall t a mid at hs
  have hlocal : ∀ j, mid.stacks (ScheduleProgram.sharedStacks j) =
      ScheduleProgram.slots words j :=
    fun j => embedState_stack _ _ _ _ ScheduleProgram.sharedStacks.injective j
  have hframe : ∀ i, (¬ ∃ j, ScheduleProgram.sharedStacks j = i) →
      mid.stacks i = a.stacks i := by
    intro i hi
    exact embedState_stack_frame _ _ _ _ i hi
  let D := 1220 * W + t + 1
  have htotal : stackBits mid.stacks ≤ D := by
    have hgrowth := trace_dataBits _
      (compiled_halt_trace hs ABI.countStack ABI.answerStack)
    have hstart := StreamResources.dataBits_le_mul
      (a.withPC (some (compiled ScheduleProgram.readySharedCall
        ABI.countStack ABI.answerStack).entry)) hwidth
    change stackBits mid.stacks ≤ stackBits a.stacks + (t + 1) at hgrowth
    change stackBits a.stacks ≤ 1220 * W at hstart
    dsimp [D]
    omega
  have hmid : ∀ i, (mid.stacks i).length ≤ D := by
    intro i
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((mid.stacks j).length))
      (Finset.mem_univ i)).trans htotal
  obtain ⟨u, b, hu, he, hclear, hkeep, _⟩ := clearSequence_eval [1, 2, 3, 4] mid D hmid
  refine ⟨t + u, b, words 5, hs.seq he, by simpa [hv] using h5,
    hlen5.trans (by simpa [hv] using (sparsify_parameters_le_input n).1), ?_, ?_⟩
  · funext i
    by_cases hi : i = 266
    · subst i
      rw [hkeep _ (by decide), Function.update_self]
      simpa [ScheduleProgram.slots] using hlocal 5
    rw [Function.update_of_ne hi]
    by_cases hc : i ∈ ([1, 2, 3, 4] : List (Fin 1220))
    · rw [hclear i hc]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · have hp := hports (1 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 1 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (2 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 2 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (3 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 3 (by decide) (by decide)] at hp
        simpa using hp.symm
      · have hp := hports (4 : Fin 32)
        rw [ScheduleProgram.sharedStacks_other 4 (by decide) (by decide)] at hp
        simpa using hp.symm
    rw [hkeep i hc]
    by_cases hp : ∃ j, ScheduleProgram.sharedStacks j = i
    · obtain ⟨j, rfl⟩ := hp
      rw [hlocal, hports]
      by_cases hj0 : j = 0
      · subst j
        simpa [ScheduleProgram.slots, Fin.coe_ofNat_eq_mod] using h0
      by_cases hj5 : j = 5
      · subst j
        exact (hi ScheduleProgram.sharedStacks_output).elim
      have hvj : (ScheduleProgram.sharedStacks j).val = j.val := by
        simp only [scheduleStacks_val, ite_eq_right hj0, ite_eq_right hj5]
      have hlow : 6 ≤ j.val := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Fin.ext_iff] at hc
        rw [hvj] at hc
        have hzero : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hfive : j.val ≠ 5 := fun h => hj5 (Fin.ext h)
        norm_num at hc
        omega
      simp [ScheduleProgram.slots, show ¬j.val < 6 by omega, hj0]
    · exact hframe i hp
  · simp only [List.length_cons, List.length_nil] at hu
    dsimp [D] at hu
    rw [hv] at htime
    omega

theorem setupAfterFrontend_eval_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        Eval (setupAfterFrontend k) steps a b ∧ SetupReady k F b ∧
        steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨K, hK⟩ := DisjointReuse.SparseBudgetProgram.commandCost_polynomial k
  refine ⟨9 * (216 * 10000002) + 9782 + K, by omega, ?_⟩
  intro n F binary a ha hv hlen hn hs
  have hsports : ∀ j : Fin 32, a.stacks (ScheduleProgram.sharedStacks j) =
      if j = 0 then binary else [] := by
    intro j
    by_cases h0 : j = 0
    · subst j
      simpa using ha.dimension
    rw [ite_eq_right h0]
    apply ha.blank
    · intro h
      exact scheduleStacks_off ABI.countStack (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact scheduleStacks_off 258 (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact scheduleStacks_off 265 (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      exact h0 (ScheduleProgram.sharedStacks.injective
        (h.trans ScheduleProgram.sharedStacks_input.symm))
  obtain ⟨t, c, s, hc, hvs, hls, hcs, ht⟩ := schedule_clear_eval n binary a hv hn
    (Encoding.formulaBitLength F + 1) hsports (frontendReady_stack_bound F binary a ha hlen)
  have hbports : ∀ j : Fin 32, c.stacks (budgetStacks j) = if j = 0 then s else [] := by
    intro j
    rw [hcs]
    by_cases h0 : j = 0
    · subst j
      rw [budgetStacks_zero, Function.update_self]
      rfl
    rw [ite_eq_right h0, Function.update_of_ne]
    · apply ha.blank
      · intro h
        exact budgetStacks_off ABI.countStack (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 258 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 265 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
      · intro h
        exact budgetStacks_off 267 (by decide) (by decide) (by decide) (by decide) ⟨j, h⟩
    · intro h
      apply h0
      exact budgetStacks.injective (h.trans budgetStacks_zero.symm)
  obtain ⟨u, b, M, B, hb, hu, hM, hB, hbp, hbf⟩ := budgetCall_eval k hk s c hbports
  have hframe (i : Fin 1220) (hi : 32 ≤ i.val)
      (h266 : i ≠ 266) (h259 : i ≠ 259) (h264 : i ≠ 264) :
      b.stacks i = a.stacks i := by
    rw [hbf i (budgetStacks_off i hi h266 h259 h264), hcs,
      Function.update_of_ne h266]
  have hb266 : b.stacks 266 = s := by simpa using hbp 0
  have hb259 : b.stacks 259 = M := by simpa using hbp 1
  have hb264 : b.stacks 264 = B := by simpa using hbp 2
  refine ⟨t + u, b, ?_, ?_, ?_⟩
  · exact hc.seq hb
  · constructor
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.input
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.header
    · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans ha.body
    · rw [hframe _ (by decide) (by decide) (by decide) (by decide), ha.dimension]
      exact hv
    · rw [hframe _ (by decide) (by decide) (by decide) (by decide), ha.dimension]
      exact hlen.trans (Nat.le_succ _)
    · rw [hb266]
      exact hvs
    · rw [hb259, hM, hvs]
    · rw [hb264, hb259]
      exact hB
    · intro i hi h258 h265 h267 h266 h259 h264
      by_cases hp : ∃ j, budgetStacks j = i
      · obtain ⟨j, rfl⟩ := hp
        rw [hbp]
        split_ifs with h0 h1 h2
        · subst j
          exact (h266 budgetStacks_zero).elim
        · subst j
          exact (h259 budgetStacks_one).elim
        · subst j
          exact (h264 budgetStacks_two).elim
        · rfl
      · rw [hbf i hp, hcs, Function.update_of_ne h266]
        exact ha.blank i hi h258 h265 h267
  · let P := (Encoding.formulaBitLength F + 1) ^ 3
    have hLn := Encoding.numVariables_le_formulaBitLength F
    have hlinear : Encoding.formulaBitLength F + 1 ≤ P := Nat.le_self_pow (by decide) _
    have hone : 1 ≤ P := Nat.one_le_pow' 3 _
    have harg : n + binary.length + 6 ≤ 6 * (Encoding.formulaBitLength F + 1) := by omega
    have hcube := Nat.pow_le_pow_left harg 3
    rw [mul_pow] at hcube
    have hschedule : t ≤ (9 * (216 * 10000002) + 9780) * P := by
      dsimp [P] at hlinear hone ⊢
      nlinarith only [ht, hcube, hlinear, hone]
    have hpositive : 0 < toNat s := by omega
    have hbudget := hK s hpositive
    have hsword : (s.length + 1) ^ 3 ≤ P :=
      Nat.pow_le_pow_left (by omega) 3
    have hbudget' : u ≤ (K + 1) * P := by
      have hmul := Nat.mul_le_mul_left K hsword
      nlinarith only [hu, hbudget, hmul, hone]
    change _ ≤ (9 * (216 * 10000002) + 9782 + K) * P
    nlinarith only [hschedule, hbudget', hone]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval_oai
