-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:17:23.417607+00:00
-- url     : https://prove2.me/submissions/df6c7bd3-51e1-42a5-9285-56e766f030f5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace Compare

/-- The final borrow is the strict comparison, even for unequal word lengths. -/
theorem carry_iff (xs ys : List Bool) (c : Bool) :
    carry c xs ys = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys + bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [carry, bitVal]
    | cons b ys ih =>
      rw [carry, ih]
      cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

private theorem update_left (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 0 zs = operandStacks zs ys := by
  funext i
  fin_cases i <;> simp [operandStacks]

private theorem update_right (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 1 zs = operandStacks xs zs := by
  funext i
  fin_cases i <;> simp [operandStacks]

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Option Bool) :
    roundRegs regs a b 0 = borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [borrowBit]

private theorem round_nil_cons (regs : Fin 8 → Bool) (b : Bool) (ys : List Bool) :
    Trace program 10 (cfg (some 1) regs [] (b :: ys))
      (cfg (some 1) (roundRegs regs none (some b)) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_nil (regs : Fin 8 → Bool) (a : Bool) (xs : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) [])
      (cfg (some 1) (roundRegs regs (some a) none) xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_cons (regs : Fin 8 → Bool) (a b : Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) (b :: ys))
      (cfg (some 1) (roundRegs regs (some a) (some b)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

/-- A concrete nonterminal round, including its branch instruction. -/
theorem round_trace (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    Trace program 10 (cfg (some 1) regs xs ys)
      (cfg (some 1) (roundRegs regs xs.head? ys.head?) xs.tail ys.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons b ys => exact round_nil_cons regs b ys
  | cons a xs =>
    cases ys with
    | nil => exact round_cons_nil regs a xs
    | cons b ys => exact round_cons_cons regs a b xs ys

theorem exit_trace (regs : Fin 8 → Bool) :
    Trace program 5 (cfg (some 1) regs [] []) (cfg none (exitRegs regs) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, exitRegs, readRegs, update_left, update_right,
    Function.update_apply]

/-- Exact instruction count for the data-dependent loop. -/
theorem loop_trace (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 5)
        (cfg (some 1) regs xs ys) (cfg none rf [] []) ∧
      rf 0 = carry (regs 0) xs ys := by
  induction xs generalizing ys regs with
  | nil =>
    induction ys generalizing regs with
    | nil =>
      exact ⟨exitRegs regs, by simpa using exit_trace regs, by simp [carry]⟩
    | cons b ys ih =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs none (some b))
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs [] (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) none) []
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) [] (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
    | cons b ys =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) (some b)) ys
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb

/-- Complete comparator contract. Leading zero bits and unequal widths are allowed. -/
theorem run (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 6)
        (cfg (some program.entry) regs xs ys) (cfg none rf [] []) ∧
      (rf 0 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf, hr, hb⟩ := loop_trace (Function.update regs 0 false) xs ys
  refine ⟨rf, ?_, ?_⟩
  · have he : Trace program 1 (cfg (some program.entry) regs xs ys)
        (cfg (some 1) (Function.update regs 0 false) xs ys) := by
      exact .cons (by rfl) (.refl _)
    convert he.trans hr using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hb]
    simpa only [Function.update_self, bitVal_false, Nat.add_zero] using carry_iff xs ys false

end Compare

open StructuredProgram

private theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hb

private theorem embed_restrict {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    StructuredCalls.embedState register stack a (restrictState register stack a) = a := by
  unfold StructuredCalls.embedState restrictState
  change State.mk (Function.extend register (a.regs ∘ register) a.regs)
    (Function.extend stack (a.stacks ∘ stack) a.stacks) = a
  rw [extend_restrict register hr, extend_restrict stack hs]

private theorem pair_eta (f : Fin 2 → List Bool) : Compare.operandStacks (f 0) (f 1) = f := by
  first | done | (funext i; fin_cases i <;> rfl)

/-- A measured comparison call on fixed injective ports, with every other
caller register and stack preserved. -/
theorem compare_call {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    ∃ b : State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram Compare.program register stack))
        (10 * max (a.stacks (stack 0)).length (a.stacks (stack 1)).length + 6) a b ∧
      (b.regs (register 0) = true ↔
        BinaryArithmetic.toNat (a.stacks (stack 0)) <
          BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ j, b.stacks (stack j) = []) := by
  obtain ⟨rf, hrun, hcmp⟩ := Compare.run (fun i => a.regs (register i))
    (a.stacks (stack 0)) (a.stacks (stack 1))
  have hstack := pair_eta (fun i => a.stacks (stack i))
  have hempty : Compare.operandStacks [] [] = (fun _ : Fin 2 => []) := by
    simpa using pair_eta (fun _ : Fin 2 => [])
  simp only [Compare.cfg, hstack, hempty] at hrun
  let localOut : State 8 2 := ⟨rf, fun _ => []⟩
  let b := StructuredCalls.embedState register stack a localOut
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.eval_call_lifted Compare.program register stack a hr hs
      (a := restrictState register stack a) (b := localOut) hrun
    rw [embed_restrict register stack hr hs a] at h
    exact h
  · simpa only [b, StructuredCalls.embedState_register register stack a localOut hr,
      localOut] using hcmp
  · exact fun i hi => StructuredCalls.embedState_register_frame register stack a localOut i hi
  · exact fun i hi => StructuredCalls.embedState_stack_frame register stack a localOut i hi
  · exact fun j => StructuredCalls.embedState_stack register stack a localOut hs j


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed Boolean-stack arithmetic in a 19-word data bank and 13 scratch stacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram

open BitProgram StructuredCalls BinaryArithmetic

theorem state_work (r : Regs) (w : Words) (i : Fin 32) (hi : 19 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 19 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 19) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 19
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 32 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]

theorem work_lower_bound (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    19 ≤ (work m hm i).val := by
  rw [work_val]
  omega

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) + toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        state_work r w (work 5 (by decide) i) (work_lower_bound 5 (by decide) i)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) * toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        state_work r w (work 5 (by decide) i) (work_lower_bound 5 (by decide) i)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem load_eval (r : Regs) (w : Words) (o : Fin 19)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he




theorem copy_eval (r : Regs) (w : Words) (a o : Fin 19) (hoa : o ≠ a) (ho : w o = []) :
    ∃ rf, Eval (copyCmd a o) (7*(w a).length+5) (state r w)
        (state rf (Function.update w o (w a))) := by
  have hh := ArithmeticCalls.copyAt_eval (port a) (port o) (work 1 (by decide) 0) (state r w)
    (by intro h; exact hoa ((Fin.castAdd_injective 19 13) h.symm))
    (work_ne_port 1 (by decide) 0 a).symm
    (work_ne_port 1 (by decide) 0 o)
    (by simpa using ho)
    (state_work r w (work 1 (by decide) 0) (work_lower_bound 1 (by decide) 0))
  refine ⟨readRegs r 0 1 none, ?_⟩
  simpa only [copyCmd, ArithmeticCalls.afterCopy, state_regs, state_port, state_update] using hh


theorem clear_eval (r : Regs) (w : Words) (a : Fin 19) :
    ∃ rf, Eval (clearCmd a) (2 * (w a).length + 3) (state r w)
      (state rf (Function.update w a [])) := by
  have h := ArithmeticExpressionSupport.clear_eval (port a) (state r w)
  refine ⟨readRegs r 0 1 none, ?_⟩
  simpa only [clearCmd, state_regs, state_port, state_update] using h

theorem logRegisters_injective : Function.Injective logRegisters :=
  Fin.castAdd_injective 3 5

theorem logStacks_injective (a : Fin 19) : Function.Injective (logStacks a) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [logStacks]

theorem resetLogRegisters_eval (r : Regs) (w : Words) :
    Eval resetLogRegisters 3 (state r w) (state (zeroLogRegs r) w) := by
  have h0 := StructuredProgram.Eval.atom (.set (0 : Fin 8) false) (state r w)
  have h1 := StructuredProgram.Eval.atom (.set (1 : Fin 8) false)
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w))
  have h2 := StructuredProgram.Eval.atom (.set (2 : Fin 8) false)
    ((StructuredProgram.Atom.set (1 : Fin 8) false).eval
      ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w)))
  simpa [resetLogRegisters, zeroLogRegs, state, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    (Eval.base h0).seq ((Eval.base h1).seq (Eval.base h2))

theorem zeroLogRegs_logRegisters (r : Regs) (i : Fin 3) :
    zeroLogRegs r (logRegisters i) = false := by
  fin_cases i <;> simp [zeroLogRegs, logRegisters]

theorem log_call_eval (r : Regs) (w : Words) (a : Fin 19)
    (hr : ∀ i : Fin 3, r (logRegisters i) = false) (ha : 0 < toNat (w a)) :
    ∃ t output, Eval (.call (ProgramLinking.liftProgram
        OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks a)))
      t (state r w) (state r (Function.update w a output)) ∧
      toNat output = Nat.clog 2 (toNat (w a)) ∧
      output.length ≤ (w a).length + 1 ∧ t ≤ 65 * ((w a).length + 2) ^ 2 := by
  obtain ⟨output, hv, hl, t, ht, he⟩ :=
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program_runs (w a)
      (by simpa only [CounterPrograms.value_eq_toNat] using ha)
  have hproj : projectState logRegisters (logStacks a) (state r w) =
      (StructuredProgram.ioState (0 : Fin 3) (w a) : StructuredProgram.State 3 3) := by
    apply CounterForPrograms.data_ext
    · funext i
      exact hr i
    · funext i
      fin_cases i
      · change (state r w).stacks (port a) = w a
        exact state_port r w a
      · change (state r w).stacks (work 2 (by decide) 0) = []
        exact state_work r w _ (work_lower_bound 2 (by decide) 0)
      · change (state r w).stacks (work 2 (by decide) 1) = []
        exact state_work r w _ (work_lower_bound 2 (by decide) 1)
  have htrace : Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program t
      ((StructuredProgram.ioState (0 : Fin 3) (w a)).withPC
        (some OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program.entry))
      ((StructuredProgram.ioState (0 : Fin 3) output).withPC none) := by
    change Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program t
      (initial OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program (w a))
      (terminal OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program output)
    exact he
  have hc := eval_call_from_state
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks a)
    (state r w) logRegisters_injective (logStacks_injective a)
    (b := StructuredProgram.ioState (0 : Fin 3) output) (by rw [hproj]; exact htrace)
  have hend : embedState logRegisters (logStacks a) (state r w)
      (StructuredProgram.ioState (0 : Fin 3) output) =
      state r (Function.update w a output) := by
    rw [← state_update r r w a output]
    apply embedState_eq_of_ports _ _ _ _ _ logRegisters_injective (logStacks_injective a)
    · intro i
      exact hr i
    · intro i _
      rfl
    · intro i
      fin_cases i
      · change Function.update (state r w).stacks (port a) output (port a) = output
        exact Function.update_self _ _ _
      · change Function.update (state r w).stacks (port a) output (work 2 (by decide) 0) = []
        rw [Function.update_of_ne (work_ne_port 2 (by decide) 0 a)]
        exact state_work r w _ (by decide)
      · change Function.update (state r w).stacks (port a) output (work 2 (by decide) 1) = []
        rw [Function.update_of_ne (work_ne_port 2 (by decide) 1 a)]
        exact state_work r w _ (by decide)
    · intro i hi
      have hne : i ≠ port a := by
        intro h
        exact hi ⟨0, h.symm⟩
      simp [hne]
  rw [hend] at hc
  exact ⟨t, output, hc, by simpa only [CounterPrograms.value_eq_toNat] using hv, hl, ht⟩

theorem clog_eval (r : Regs) (w : Words) (a o : Fin 19) (hoa : o ≠ a)
    (ho : w o = []) (ha : 0 < toNat (w a)) :
    ∃ t rf output, Eval (clogCmd a o) t (state r w)
        (state rf (Function.update w o output)) ∧
      toNat output = Nat.clog 2 (toNat (w a)) ∧
      output.length ≤ (w a).length + 1 ∧ t ≤ 80 * ((w a).length + 2) ^ 2 := by
  obtain ⟨rf, hc⟩ := copy_eval r w a o hoa ho
  have hz := resetLogRegisters_eval rf (Function.update w o (w a))
  obtain ⟨t, output, hl, hv, hlen, ht⟩ := log_call_eval (zeroLogRegs rf)
    (Function.update w o (w a)) o (zeroLogRegs_logRegisters rf)
    (by simpa using ha)
  refine ⟨(7 * (w a).length + 5) + (3 + t), zeroLogRegs rf, output, ?_, ?_, ?_, ?_⟩
  · simpa [clogCmd, Function.update_idem] using hc.seq (hz.seq hl)
  · simpa using hv
  · simpa using hlen
  · simp only [Function.update_self] at ht
    nlinarith

theorem compareStacks_injective {a b : Fin 19} (hab : a ≠ b) :
    Function.Injective (compareStacks a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks, port, Fin.ext_iff]

theorem compare_eval (r : Regs) (w : Words) (a b : Fin 19) (hab : a ≠ b) :
    ∃ rf, Eval (compareCmd a b) (10 * max (w a).length (w b).length + 6)
        (state r w) (state rf (Function.update (Function.update w a []) b [])) ∧
      (rf 0 = true ↔ toNat (w a) < toNat (w b)) := by
  obtain ⟨out, he, hv, _, hf, hz⟩ := OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram.compare_call id
    (compareStacks a b) Function.injective_id (compareStacks_injective hab) (state r w)
  have hout : out = state out.regs (Function.update (Function.update w a []) b []) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      by_cases ha : i = port a
      · subst i
        simpa [compareStacks, state, port, hab, Ne.symm hab] using hz 0
      · by_cases hb : i = port b
        · subst i
          simpa [compareStacks, state, port] using hz 1
        · have hi : ¬ ∃ j, compareStacks a b j = i := by
            rintro ⟨j, hj⟩
            fin_cases j <;> simp_all [compareStacks]
          rw [hf i hi]
          simp only [state]
          split_ifs with h
          · have hia : (⟨i.val, h⟩ : Fin 19) ≠ a := by
              intro e
              apply ha
              exact Fin.ext (congrArg (fun x : Fin 19 => x.val) e)
            have hib : (⟨i.val, h⟩ : Fin 19) ≠ b := by
              intro e
              apply hb
              exact Fin.ext (congrArg (fun x : Fin 19 => x.val) e)
            simp [hia, hib]
          · rfl
  rw [hout] at he
  refine ⟨out.regs, ?_, ?_⟩
  · simpa [compareCmd, compareStacks] using he
  · simpa [compareStacks] using hv


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram
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

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem four_le_depthConstant (k M : ℕ) (hk : 2 ≤ k) : 4 ≤ depthConstant k M := by
  have hsum : 1 ≤ ∑ j ∈ range (k - 1), (3 * M) ^ j := by
    simpa using (Finset.single_le_sum (f := fun j => (3 * M) ^ j)
      (fun _ _ => Nat.zero_le _) (show 0 ∈ range (k - 1) from mem_range.mpr (by omega)))
  exact Nat.mul_le_mul_left 4 hsum

theorem four_le_rightConstant (k : ℕ) (hk : 2 ≤ k) : 4 ≤ rightConstant k := by
  simpa [depthConstant, rightConstant] using four_le_depthConstant k 1 hk


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

theorem Arithmetic.eval (op : Arithmetic) (r : Regs) (w : Words)
    (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word, Eval (op.command a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = op.value (toNat (w a)) (toNat (w b)) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  cases op with
  | add => exact add_eval r w a b o hoa hob ho
  | multiply => exact multiply_eval r w a b o hoa hob ho

theorem replace_eval (op : Arithmetic) (r : Regs) (w : Words)
    (a b o tmp : Fin 19) (hta : tmp ≠ a) (htb : tmp ≠ b)
    (hto : tmp ≠ o) (ht : w tmp = []) :
    ∃ t rf word, Eval (replaceCmd op a b o tmp hta htb) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = op.value (toNat (w a)) (toNat (w b)) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 150 * ((w a).length + (w b).length + (w o).length + 2) ^ 2 := by
  obtain ⟨t, r₁, word, he, hv, hl, htime⟩ := op.eval r w a b tmp hta htb ht
  obtain ⟨r₂, hc⟩ := clear_eval r₁ (Function.update w tmp word) o
  obtain ⟨r₃, hp⟩ := copy_eval r₂ (Function.update (Function.update w tmp word) o [])
    tmp o hto.symm (by simp)
  obtain ⟨r₄, hz⟩ := clear_eval r₃
    (Function.update (Function.update (Function.update w tmp word) o []) o word) tmp
  have hframe : Function.update
      (Function.update (Function.update (Function.update w tmp word) o []) o word) tmp [] =
      Function.update w o word := by
    funext i
    by_cases hi : i = tmp
    · subst i
      simp [hto, ht]
    · by_cases hio : i = o
      · subst i
        simp [Ne.symm hto]
      · simp [hi, hio]
  refine ⟨t + (2 * (w o).length + 3 +
      (7 * word.length + 5 + (2 * word.length + 3))), r₄, word, ?_, hv, hl, ?_⟩
  · have hp' := hp
    simp only [Function.update_of_ne hto, Function.update_self] at hp'
    have hc' := hc
    simp only [Function.update_of_ne hto.symm] at hc'
    have hz' := hz
    simp only [Function.update_of_ne hto, Function.update_self] at hz'
    simpa only [replaceCmd, hframe] using he.seq (hc'.seq (hp'.seq hz'))
  · nlinarith

theorem hornerStep_eval (r : Regs) (w : Words) (ht : w 3 = []) :
    ∃ t rf word, Eval hornerStep t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 2) * toNat (w 12) + toNat (w 5) ∧
      word.length ≤ (w 2).length + (w 12).length + (w 5).length + 2 ∧
      t ≤ 1200 * ((w 2).length + (w 12).length + (w 5).length + 2) ^ 2 := by
  obtain ⟨t₁, r₁, word₁, he₁, hv₁, hl₁, ht₁⟩ :=
    replace_eval .multiply r w 2 12 2 3 (by decide) (by decide) (by decide) ht
  obtain ⟨t₂, r₂, word₂, he₂, hv₂, hl₂, ht₂⟩ :=
    replace_eval .add r₁ (Function.update w 2 word₁) 2 5 2 3
      (by decide) (by decide) (by decide) (by simpa using ht)
  simp only [Function.update_self, Function.update_of_ne (by decide : (5 : Fin 19) ≠ 2),
    Arithmetic.value] at hv₂ hl₂ ht₂
  refine ⟨t₁ + t₂, r₂, word₂, ?_, ?_, by omega, ?_⟩
  · simpa only [hornerStep, Function.update_idem] using he₁.seq he₂
  · simpa only [Arithmetic.value, hv₁] using hv₂
  · let L := (w 2).length + (w 12).length + (w 5).length + 2
    have h₁ : 2 * (w 2).length + (w 12).length + 2 ≤ 2 * L := by dsimp [L]; omega
    have h₂ : 2 * word₁.length + (w 5).length + 2 ≤ 2 * L := by dsimp [L]; omega
    have hs₁ := Nat.pow_le_pow_left h₁ 2
    have hs₂ := Nat.pow_le_pow_left h₂ 2
    dsimp [L] at hs₁ hs₂
    nlinarith

/-- Horner's recurrence is unrolled in the finite control. The summation below
counts its actual arithmetic traces, with no unit-cost natural multiplication. -/
theorem horner_eval (j : ℕ) (r : Regs) (w : Words) (ht : w 3 = [])
    (hu : toNat (w 5) = 1) :
    ∃ t rf word, Eval (horner j) t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 12) ^ j * toNat (w 2) +
        ∑ i ∈ Finset.range j, toNat (w 12) ^ i ∧
      word.length ≤ (w 2).length + j * ((w 12).length + (w 5).length + 2) ∧
      t ≤ 1200 * ∑ i ∈ Finset.range j,
        ((w 2).length + (i + 1) * ((w 12).length + (w 5).length + 2) + 2) ^ 2 := by
  induction j with
  | zero =>
    refine ⟨0, r, w 2, ?_, ?_, ?_, ?_⟩
    · simpa only [horner, Function.update_eq_self] using
        Eval.base (StructuredProgram.Eval.skip (state r w))
    · simp
    · simp
    · simp
  | succ j ih =>
    obtain ⟨t₁, r₁, word₁, he₁, hv₁, hl₁, ht₁⟩ := ih
    obtain ⟨t₂, r₂, word₂, he₂, hv₂, hl₂, ht₂⟩ :=
      hornerStep_eval r₁ (Function.update w 2 word₁) (by simpa using ht)
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (12 : Fin 19) ≠ 2),
      Function.update_of_ne (by decide : (5 : Fin 19) ≠ 2)] at hv₂ hl₂ ht₂
    refine ⟨t₁ + t₂, r₂, word₂, ?_, ?_, ?_, ?_⟩
    · simpa only [horner, Function.update_idem] using he₁.seq he₂
    · rw [hv₂, hu, hv₁, geom_sum_succ, pow_succ]
      ring
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · have harg : word₁.length + (w 12).length + (w 5).length + 2 ≤
          (w 2).length + (j + 1) * ((w 12).length + (w 5).length + 2) + 2 := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hs := Nat.pow_le_pow_left harg 2
      rw [Finset.sum_range_succ, Nat.mul_add]
      omega

/-- Exact execution of the expensive test, including its arithmetic costs and cleanup. -/
theorem budgetTest_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s M : List Bool)
    (hM : 0 < toNat M) :
    ∃ t rf, Eval (budgetTest k) t (state r (prepared k s M))
        (state rf (prepared k s M)) ∧
      (rf 0 = true ↔ toNat M < SparseCharging.rightConstant k *
        Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s) ∧
      t ≤ 10000 * (k + 1) * candidateWidth k s M ^ 2 := by
  let w := prepared k s M
  obtain ⟨t₁, r₁, base, he₁, hv₁, hl₁, ht₁⟩ :=
    multiply_eval r w 1 4 12 (by decide) (by decide) (by simp [w, prepared])
  let w₁ := Function.update w 12 base
  obtain ⟨t₂, r₂, sum, he₂, hv₂, hl₂, ht₂⟩ := horner_eval (k - 1) r₁ w₁
    (by simp [w₁, w, prepared])
    (by simp [w₁, w, prepared, BinaryArithmetic.toNat, BinaryArithmetic.bitVal])
  let w₂ := Function.update w₁ 2 sum
  obtain ⟨t₃, r₃, scaled, he₃, hv₃, hl₃, ht₃⟩ :=
    replace_eval .multiply r₂ w₂ 2 6 2 3 (by decide) (by decide) (by decide)
      (by simp [w₂, w₁, w, prepared])
  let w₃ := Function.update w₂ 2 scaled
  obtain ⟨t₄, r₄, arg, he₄, hv₄, hl₄, ht₄⟩ :=
    replace_eval .multiply r₃ w₃ 2 1 2 3 (by decide) (by decide) (by decide)
      (by simp [w₃, w₂, w₁, w, prepared])
  have hbase : toNat base = toNat M * 3 := by
    simpa [w, prepared, ArithmeticExpressionSupport.bits_value] using hv₁
  have hsum : toNat sum = ∑ i ∈ Finset.range (k - 1), (3 * toNat M) ^ i := by
    simpa [w₁, w, prepared, hbase, Nat.mul_comm] using hv₂
  have hscaled : toNat scaled = toNat sum * 16 := by
    simpa [w₂, w₁, w, prepared, Arithmetic.value, ArithmeticExpressionSupport.bits_value] using hv₃
  have harg : toNat arg = 4 * SparseCharging.depthConstant k (toNat M) * toNat M := by
    have hv : toNat arg = toNat scaled * toNat M := by
      simpa [Arithmetic.value, w₃, w₂, w₁, w, prepared] using hv₄
    rw [hv, hscaled, hsum, SparseCharging.depthConstant]
    ring
  have hargpos : 0 < toNat arg := by
    rw [harg]
    have hC : 0 < SparseCharging.depthConstant k (toNat M) := by
      have := SparseBudget.four_le_depthConstant k (toNat M) hk
      omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC) hM
  let w₄ := Function.update w₃ 2 arg
  obtain ⟨t₅, r₅, logarithm, he₅, hv₅, hl₅, ht₅⟩ := clog_eval r₄ w₄ 2 10 (by decide)
    (by simp [w₄, w₃, w₂, w₁, w, prepared]) (by simpa [w₄] using hargpos)
  let w₅ := Function.update w₄ 10 logarithm
  obtain ⟨t₆, r₆, product, he₆, hv₆, hl₆, ht₆⟩ :=
    multiply_eval r₅ w₅ 10 7 11 (by decide) (by decide)
      (by simp [w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₆ := Function.update w₅ 11 product
  obtain ⟨t₇, r₇, threshold, he₇, hv₇, hl₇, ht₇⟩ :=
    multiply_eval r₆ w₆ 11 0 9 (by decide) (by decide)
      (by simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₇ := Function.update w₆ 9 threshold
  obtain ⟨r₈, he₈⟩ := copy_eval r₇ w₇ 1 8 (by decide)
    (by simp [w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₈ := Function.update w₇ 8 (w₇ 1)
  obtain ⟨r₉, he₉⟩ := clear_eval r₈ w₈ 2
  let w₉ := Function.update w₈ 2 []
  obtain ⟨r₁₀, he₁₀⟩ := clear_eval r₉ w₉ 10
  let w₁₀ := Function.update w₉ 10 []
  obtain ⟨r₁₁, he₁₁⟩ := clear_eval r₁₀ w₁₀ 11
  let w₁₁ := Function.update w₁₀ 11 []
  obtain ⟨r₁₂, he₁₂⟩ := clear_eval r₁₁ w₁₁ 12
  let w₁₂ := Function.update w₁₁ 12 []
  obtain ⟨rf, he₁₃, hflag⟩ := compare_eval r₁₂ w₁₂ 8 9 (by decide)
  have hframe : Function.update (Function.update w₁₂ 8 []) 9 [] = w := by
    funext i
    fin_cases i <;> simp [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared]
  have hrun := he₁.seq (he₂.seq (he₃.seq (he₄.seq
      (he₅.seq (he₆.seq (he₇.seq (he₈.seq (he₉.seq (he₁₀.seq (he₁₁.seq
        (he₁₂.seq he₁₃)))))))))))
  refine ⟨_, rf, by simpa only [budgetTest, hframe] using hrun, ?_, ?_⟩
  · have hlog : toNat logarithm = Nat.clog 2
        (4 * SparseCharging.depthConstant k (toNat M) * toNat M) := by
      simpa [w₄, harg] using hv₅
    have hprod : toNat product = toNat logarithm * SparseCharging.rightConstant k := by
      simpa [w₅, w₄, w₃, w₂, w₁, w, prepared, ArithmeticExpressionSupport.bits_value] using hv₆
    have hthresh : toNat threshold = SparseCharging.rightConstant k *
        Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s := by
      simpa [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared, hprod, hlog, Nat.mul_comm] using hv₇
    simpa [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared, hthresh]
      using hflag
  · let L := candidateWidth k s M
    have hL : 20 ≤ L := by dsimp [L, candidateWidth]; omega
    simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared] at hl₁ hl₂ hl₃ hl₄ hl₅ hl₆ hl₇
    simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared] at ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇
    have hbase : base.length ≤ M.length + 3 := by simpa using hl₁
    have hH : sum.length ≤ (k - 1) * (M.length + 6) := by
      exact hl₂.trans (Nat.mul_le_mul_left _ (by omega))
    have hsumL : sum.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hscaledL : scaled.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hargL : arg.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hlogL : logarithm.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hprodL : product.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hthreshL : threshold.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hbaseL : base.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hML : M.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hsL : s.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hΓL : (SparseCharging.rightConstant k).bits.length ≤ L := by
      dsimp [L, candidateWidth]; omega
    have hsquare (a b : ℕ) (h : a ≤ b * L) : a ^ 2 ≤ b ^ 2 * L ^ 2 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left h 2
    have hc₁ : t₁ ≤ 100 * L ^ 2 := by
      have harg : M.length + 3 ≤ L := by dsimp [L, candidateWidth]; omega
      have := Nat.pow_le_pow_left harg 2
      nlinarith only [ht₁, this]
    have hc₂ : t₂ ≤ 1200 * (k - 1) * L ^ 2 := by
      have hsum : (∑ i ∈ Finset.range (k - 1), (0 + (i + 1) * (base.length + 1 + 2) + 2) ^ 2) ≤
          (k - 1) * L ^ 2 := by
        calc
          _ ≤ ∑ _i ∈ Finset.range (k - 1), L ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.pow_le_pow_left
            have hi' : i + 1 ≤ k - 1 := by have := Finset.mem_range.mp hi; omega
            have hh := Nat.mul_le_mul hi' (show base.length + 1 + 2 ≤ M.length + 6 by omega)
            dsimp [L, candidateWidth]
            omega
          _ = _ := by simp
      simp only [Nat.zero_add] at hsum
      nlinarith only [ht₂, hsum]
    have hc₃ : t₃ ≤ 1350 * L ^ 2 := by
      have := hsquare (sum.length + 5 + sum.length + 2) 3 (by omega)
      nlinarith only [ht₃, this]
    have hc₄ : t₄ ≤ 2400 * L ^ 2 := by
      have := hsquare (scaled.length + M.length + scaled.length + 2) 4 (by omega)
      nlinarith only [ht₄, this]
    have hc₅ : t₅ ≤ 320 * L ^ 2 := by
      have := hsquare (arg.length + 2) 2 (by omega)
      nlinarith only [ht₅, this]
    have hc₆ : t₆ ≤ 900 * L ^ 2 := by
      have := hsquare (logarithm.length + (SparseCharging.rightConstant k).bits.length + 1)
        3 (by omega)
      nlinarith only [ht₆, this]
    have hc₇ : t₇ ≤ 900 * L ^ 2 := by
      have := hsquare (product.length + s.length + 1) 3 (by omega)
      nlinarith only [ht₇, this]
    have hmax : max M.length threshold.length ≤ L := max_le hML hthreshL
    have hself : L ≤ L ^ 2 := by nlinarith only [hL]
    simp [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared]
    change _ ≤ 10000 * (k + 1) * L ^ 2
    have hkl : (k - 1) * L ^ 2 ≤ k * L ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    nlinarith only [hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hmax, hself,
      hML, hargL, hlogL, hprodL, hbaseL, hkl, hL]

theorem test_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s M : List Bool)
    (hM : 0 < toNat M) :
    ∃ t rf, Eval (test k) t (state r (prepared k s M))
        (state rf (prepared k s M)) ∧
      (rf 0 = true ↔ toNat M < SparseCharging.rightConstant k ∨
        toNat M < SparseCharging.rightConstant k *
          Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s) ∧
      t ≤ 12000 * (k + 1) * candidateWidth k s M ^ 2 := by
  let w := prepared k s M
  obtain ⟨r₁, he₁⟩ := copy_eval r w 1 8 (by decide) (by simp [w, prepared])
  let w₁ := Function.update w 8 (w 1)
  obtain ⟨r₂, he₂⟩ := copy_eval r₁ w₁ 7 9 (by decide) (by simp [w₁, w, prepared])
  let w₂ := Function.update w₁ 9 (w₁ 7)
  obtain ⟨r₃, he₃, hf₃⟩ := compare_eval r₂ w₂ 8 9 (by decide)
  have hframe : Function.update (Function.update w₂ 8 []) 9 [] = w := by
    funext i
    fin_cases i <;> simp [w₂, w₁, w, prepared]
  rw [hframe] at he₃
  have hflag : r₃ 0 = true ↔ toNat M < SparseCharging.rightConstant k := by
    simpa [w₂, w₁, w, prepared, ArithmeticExpressionSupport.bits_value] using hf₃
  let L := candidateWidth k s M
  have hL : 20 ≤ L := by dsimp [L, candidateWidth]; omega
  have hML : M.length ≤ L := by dsimp [L, candidateWidth]; omega
  have hΓL : (SparseCharging.rightConstant k).bits.length ≤ L := by
    dsimp [L, candidateWidth]; omega
  have hmax : max M.length (SparseCharging.rightConstant k).bits.length ≤ L :=
    max_le hML hΓL
  have hself : L ≤ L ^ 2 := by nlinarith
  cases hreg : r₃ 0 with
  | false =>
    obtain ⟨t, rf, he, hf, ht⟩ := budgetTest_eval k hk r₃ s M hM
    refine ⟨_, rf, he₁.seq (he₂.seq (he₃.seq (.ite_false hreg he))), ?_, ?_⟩
    · have hn : ¬ toNat M < SparseCharging.rightConstant k := by
        intro h
        have := hflag.mpr h
        simp [hreg] at this
      simpa only [hn, false_or] using hf
    · simp [w₂, w₁, w, prepared]
      change _ ≤ 12000 * (k + 1) * L ^ 2
      change t ≤ 10000 * (k + 1) * L ^ 2 at ht
      nlinarith
  | true =>
    refine ⟨_, r₃, he₁.seq (he₂.seq (he₃.seq (.ite_true hreg
        (Eval.base (StructuredProgram.Eval.skip (state r₃ w)))))), ?_, ?_⟩
    · exact ⟨fun _ => Or.inl (hflag.mp hreg), fun _ => hreg⟩
    · simp [w₂, w₁, w, prepared]
      change _ ≤ 12000 * (k + 1) * L ^ 2
      nlinarith

theorem test_dyadic_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) (e : ℕ) :
    ∃ t rf, Eval (test k) t (state r (prepared k s (dyadicWord e)))
        (state rf (prepared k s (dyadicWord e))) ∧
      (rf 0 = true ↔ SparseBudget.parameterTest k 1 (toNat s) e = false) ∧
      t ≤ 12000 * (k + 1) * candidateWidth k s (dyadicWord e) ^ 2 := by
  obtain ⟨t, rf, he, hf, ht⟩ := test_eval k hk r s (dyadicWord e) (by simp)
  refine ⟨t, rf, he, hf.trans ?_, ht⟩
  have hΓ := SparseBudget.four_le_rightConstant k hk
  simp only [dyadicWord_value, SparseBudget.parameterTest, decide_eq_false_iff_not, one_mul]
  omega

theorem double_eval (r : Regs) (w : Words) :
    Eval double 2 (state r w)
      (state (Function.update r 0 false) (Function.update w 1 (false :: w 1))) := by
  have hs := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) (state r w))
  have hp := Eval.base (StructuredProgram.Eval.atom (.push (port 1) (0 : Fin 8))
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w)))
  have h : Eval double 2 (state r w)
      (⟨Function.update r 0 false, Function.update (state r w).stacks (port 1)
        (false :: w 1)⟩ : Data) := by
    simpa [double, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using hs.seq hp
  simpa only [state_update] using h

theorem double_prepared_eval (k : ℕ) (r : Regs) (s : List Bool) (e : ℕ) :
    Eval double 2 (state r (prepared k s (dyadicWord e)))
      (state (Function.update r 0 false) (prepared k s (dyadicWord (e + 1)))) := by
  have h := double_eval r (prepared k s (dyadicWord e))
  have heq : Function.update (prepared k s (dyadicWord e)) 1
      (false :: prepared k s (dyadicWord e) 1) = prepared k s (dyadicWord (e + 1)) := by
    funext i
    by_cases hi : i = 1
    · subst i
      simp [prepared, dyadicWord]
    · simp [hi, prepared]
  simpa only [heq] using h

/-- Termination follows from the proved first-passing index; every loop iteration
is an actual doubling trace followed by the concrete test trace. -/
theorem loop_eval (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (e left : ℕ)
    (hstop : e + left = SparseBudget.chooseExponent k 1 (toNat s) (by decide))
    (r : Regs) (hr : r 0 = true ↔ SparseBudget.parameterTest k 1 (toNat s) e = false) :
    ∃ t rf, Eval (.while 0 (.seq double (test k))) t
        (state r (prepared k s (dyadicWord e)))
        (state rf (prepared k s (dyadicWord
          (SparseBudget.chooseExponent k 1 (toNat s) (by decide))))) ∧
      t ≤ (left + 1) * (12000 * (k + 1) * candidateWidth k s
        (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) ^ 2 + 3) := by
  induction left generalizing e r with
  | zero =>
    have he : e = SparseBudget.chooseExponent k 1 (toNat s) (by decide) := by omega
    have hp := SparseBudget.chooseExponent_spec k 1 (toNat s) (by decide)
    have hrfalse : r 0 = false := by
      cases h : r 0
      · rfl
      · have hbad := hr.mp h
        rw [he, hp] at hbad
        cases hbad
    refine ⟨1, r, ?_, by omega⟩
    simpa only [he] using Eval.while_false (body := .seq double (test k)) hrfalse
  | succ left ih =>
    have he : e < SparseBudget.chooseExponent k 1 (toNat s) (by decide) := by omega
    have hfail : SparseBudget.parameterTest k 1 (toNat s) e = false := by
      have hn := Nat.find_min (SparseBudget.exists_parameter k 1 (toNat s) (by decide)) he
      cases h : SparseBudget.parameterTest k 1 (toNat s) e
      · rfl
      · exact False.elim (hn h)
    have hd := double_prepared_eval k r s e
    obtain ⟨t, r₁, ht, hf, htime⟩ := test_dyadic_eval k hk (Function.update r 0 false) s (e + 1)
    obtain ⟨u, rf, hu, hutime⟩ := ih (e + 1) (by omega) r₁ hf
    refine ⟨2 + t + u + 1, rf, Eval.while_true (hr.mpr hfail) (hd.seq ht) hu, ?_⟩
    have hwidth : candidateWidth k s (dyadicWord (e + 1)) ≤
        candidateWidth k s (dyadicWord
          (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) := by
      simp only [candidateWidth, dyadicWord_length]
      have hh := Nat.mul_le_mul_left (k - 1)
        (show e + 1 + 1 + 6 ≤
          SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 1 + 6 by omega)
      omega
    have hcost := Nat.mul_le_mul_left (12000 * (k + 1)) (Nat.pow_le_pow_left hwidth 2)
    let C := 12000 * (k + 1) * candidateWidth k s
      (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) ^ 2
    have htC : t ≤ C := htime.trans (by simpa only [C] using hcost)
    have huC : u ≤ (left + 1) * (C + 3) := by simpa only [C] using hutime
    change 2 + t + u + 1 ≤ (left + 2) * (C + 3)
    calc
      2 + t + u + 1 ≤ 3 + C + (left + 1) * (C + 3) := by omega
      _ = (left + 2) * (C + 3) := by ring

theorem initCmd_eval (k : ℕ) (r : Regs) (s : List Bool) :
    ∃ t rf, Eval (initCmd k) t (state r (inputWords s))
      (state rf (prepared k s (dyadicWord 0))) ∧
      t ≤ 2 * (SparseCharging.rightConstant k).bits.length + 18 := by
  let w := inputWords s
  obtain ⟨r₁, he₁⟩ := load_eval r w 1 [true] (by simp [w, inputWords])
  let w₁ := Function.update w 1 [true]
  obtain ⟨r₂, he₂⟩ := load_eval r₁ w₁ 4 (3 : ℕ).bits (by simp [w₁, w, inputWords])
  let w₂ := Function.update w₁ 4 (3 : ℕ).bits
  obtain ⟨r₃, he₃⟩ := load_eval r₂ w₂ 5 [true] (by simp [w₂, w₁, w, inputWords])
  let w₃ := Function.update w₂ 5 [true]
  obtain ⟨r₄, he₄⟩ := load_eval r₃ w₃ 6 (16 : ℕ).bits
    (by simp [w₃, w₂, w₁, w, inputWords])
  let w₄ := Function.update w₃ 6 (16 : ℕ).bits
  obtain ⟨rf, he₅⟩ := load_eval r₄ w₄ 7 (SparseCharging.rightConstant k).bits
    (by simp [w₄, w₃, w₂, w₁, w, inputWords])
  have hframe : Function.update w₄ 7 (SparseCharging.rightConstant k).bits =
      prepared k s (dyadicWord 0) := by
    funext i
    fin_cases i <;> simp [w₄, w₃, w₂, w₁, w, inputWords, prepared, dyadicWord]
  refine ⟨_, rf, by
    simpa only [initCmd, hframe] using he₁.seq (he₂.seq (he₃.seq (he₄.seq he₅))), ?_⟩
  simp only [bits_three_length, bits_sixteen_length, List.length_singleton]
  omega

theorem search_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) :
    ∃ t rf, Eval (search k) t (state r (inputWords s))
      (state rf (prepared k s (dyadicWord
        (SparseBudget.chooseExponent k 1 (toNat s) (by decide))))) ∧
      t ≤ searchCost k s := by
  obtain ⟨t₁, r₁, he₁, ht₁⟩ := initCmd_eval k r s
  obtain ⟨t₂, r₂, he₂, hf₂, ht₂⟩ := test_dyadic_eval k hk r₁ s 0
  obtain ⟨t₃, rf, he₃, ht₃⟩ := loop_eval k hk s 0
    (SparseBudget.chooseExponent k 1 (toNat s) (by decide)) (by omega) r₂ hf₂
  refine ⟨t₁ + (t₂ + t₃), rf, he₁.seq (he₂.seq he₃), ?_⟩
  have hwidth : candidateWidth k s (dyadicWord 0) ≤ candidateWidth k s
      (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) := by
    simp only [candidateWidth, dyadicWord_length]
    have := Nat.mul_le_mul_left (k - 1)
      (show 0 + 1 + 6 ≤ SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 1 + 6 by omega)
    omega
  have hcost := Nat.mul_le_mul_left (12000 * (k + 1)) (Nat.pow_le_pow_left hwidth 2)
  dsimp [searchCost]
  nlinarith

theorem boundPowers_eval (j : ℕ) (r : Regs) (w : Words) (ht : w 3 = []) :
    ∃ t rf word, Eval (boundPowers j) t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 2) * toNat (w 1) ^ j ∧
      word.length ≤ (w 2).length + j * ((w 1).length + 1) ∧
      t ≤ 600 * j * ((w 2).length + j * ((w 1).length + 1) + 2) ^ 2 := by
  induction j with
  | zero =>
    refine ⟨0, r, w 2, ?_, ?_, ?_, ?_⟩
    · simpa only [boundPowers, Function.update_eq_self] using
        Eval.base (StructuredProgram.Eval.skip (state r w))
    · simp
    · simp
    · simp
  | succ j ih =>
    obtain ⟨t, r₁, word, he, hv, hl, htime⟩ := ih
    obtain ⟨u, rf, word', he', hv', hl', htime'⟩ := replace_eval .multiply r₁
      (Function.update w 2 word) 2 1 2 3 (by decide) (by decide) (by decide)
      (by simpa using ht)
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 19) ≠ 2), Arithmetic.value] at hv' hl' htime'
    refine ⟨t + u, rf, word', ?_, ?_, ?_, ?_⟩
    · simpa only [boundPowers, Function.update_idem] using he.seq he'
    · rw [hv', hv, pow_succ]
      ring
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · have hstep : word.length + (w 1).length + word.length + 2 ≤
          2 * ((w 2).length + (j + 1) * ((w 1).length + 1) + 2) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hs := Nat.pow_le_pow_left hstep 2
      have hmono : ((w 2).length + j * ((w 1).length + 1) + 2) ^ 2 ≤
          ((w 2).length + (j + 1) * ((w 1).length + 1) + 2) ^ 2 :=
        Nat.pow_le_pow_left (by simp only [Nat.add_mul, Nat.one_mul]; omega) 2
      have hm := Nat.mul_le_mul_left (600 * j) hmono
      nlinarith

/-- The two parameter words are returned in ports one and two; the input in port
zero is preserved for the calling algorithm. All remaining 29 stacks are empty. -/
theorem command_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) :
    ∃ t rf M B, Eval (command k) t (state r (inputWords s))
        (state rf (outputWords s M B)) ∧
      toNat M = SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
      toNat B = 4 * toNat M ^ (k - 1) ∧ t ≤ commandCost k s := by
  let M := dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))
  obtain ⟨t₁, r₁, he₁, ht₁⟩ := search_eval k hk r s
  let w := prepared k s M
  obtain ⟨r₂, he₂⟩ := load_eval r₁ w 2 (4 : ℕ).bits (by simp [w, prepared])
  let w₂ := Function.update w 2 (4 : ℕ).bits
  obtain ⟨t₃, r₃, B, he₃, hv₃, _, ht₃⟩ := boundPowers_eval (k - 1) r₂ w₂
    (by simp [w₂, w, prepared])
  let w₃ := Function.update w₂ 2 B
  obtain ⟨r₄, he₄⟩ := clear_eval r₃ w₃ 4
  let w₄ := Function.update w₃ 4 []
  obtain ⟨r₅, he₅⟩ := clear_eval r₄ w₄ 5
  let w₅ := Function.update w₄ 5 []
  obtain ⟨r₆, he₆⟩ := clear_eval r₅ w₅ 6
  let w₆ := Function.update w₅ 6 []
  obtain ⟨rf, he₇⟩ := clear_eval r₆ w₆ 7
  have hframe : Function.update w₆ 7 [] = outputWords s M B := by
    funext i
    fin_cases i <;> simp [w₆, w₅, w₄, w₃, w₂, w, prepared, outputWords]
  have hrun := he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq (he₆.seq he₇)))))
  refine ⟨_, rf, M, B, by simpa only [command, hframe] using hrun,
    by simp [M, SparseBudget.chooseM], ?_, ?_⟩
  · simpa [w₂, w, prepared, ArithmeticExpressionSupport.bits_value] using hv₃
  · simp [w₂, w, prepared, M] at ht₃
    let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
    have harg : 3 + (k - 1) * (N + 1 + 1) + 2 ≤ 5 + k * (N + 2) := by
      rw [show N + 1 + 1 = N + 2 by omega]
      have := Nat.mul_le_mul_right (N + 2) (Nat.sub_le k 1)
      omega
    have hbudget := Nat.mul_le_mul (Nat.mul_le_mul_left 600 (Nat.sub_le k 1))
      (Nat.pow_le_pow_left harg 2)
    change t₃ ≤ 600 * (k - 1) * (3 + (k - 1) * (N + 1 + 1) + 2) ^ 2 at ht₃
    have htime₃ := ht₃.trans hbudget
    simp [w₆, w₅, w₄, w₃, w₂, w, prepared]
    dsimp [commandCost]
    change _ ≤ searchCost k s + 600 * k * (5 + k * (N + 2)) ^ 2 + _ + _
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
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

theorem budgetCall_eval_oai (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (a : State 80 1220)
    (hports : ∀ j, a.stacks (budgetStacks j) = if j = 0 then s else []) :
    ∃ steps b M B,
      Eval (budgetCall k) steps a b ∧
      steps ≤ DisjointReuse.SparseBudgetProgram.commandCost k s + 1 ∧
      toNat M = DisjointReuse.SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
      toNat B = 4 * toNat M ^ (k - 1) ∧
      (∀ j, b.stacks (budgetStacks j) = if j = 0 then s else if j = 1 then M
        else if j = 2 then B else []) ∧
      (∀ i, (¬ ∃ j, budgetStacks j = i) → b.stacks i = a.stacks i) := by
  let localData := projectState (Fin.castAdd 72) budgetStacks a
  obtain ⟨t, rf, M, B, he, hM, hB, ht⟩ :=
    DisjointReuse.SparseBudgetProgram.command_eval k hk localData.regs s
  have hstart : DisjointReuse.ParametersProgram.state localData.regs
      (DisjointReuse.SparseBudgetProgram.inputWords s) = localData := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      have hp := hports i
      change _ = a.stacks (budgetStacks i)
      rw [hp]
      fin_cases i <;> rfl
  have htrace := compiled_halt_trace he (DisjointReuse.ParametersProgram.port 0)
    (DisjointReuse.ParametersProgram.port 1)
  rw [hstart] at htrace
  let out := DisjointReuse.ParametersProgram.state rf
    (DisjointReuse.SparseBudgetProgram.outputWords s M B)
  refine ⟨t + 1, embedState (Fin.castAdd 72) budgetStacks a out, M, B,
    eval_call_from_state _ _ _ a (Fin.castAdd_injective 8 72)
      budgetStacks.injective htrace, by omega, hM, hB, ?_, ?_⟩
  · intro j
    rw [embedState_stack _ _ _ _ budgetStacks.injective]
    fin_cases j <;> rfl
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval_oai
