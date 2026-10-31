-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:36:17.602187+00:00
-- url     : https://prove2.me/submissions/61a2efef-5ed6-4e8c-a745-b12228d0b3b0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyRound_scan_minimum
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyRun_staged_boundary_attempt
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace_rounds_halt_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyStagedSpace_attempt_halt_space

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- A singleton shape contains exactly the one physical payload word. -/
theorem tuple_eq_singleton_flatten {words : List (List Bool)} {width : ℕ}
    (hshape : words.map List.length = [width]) : words = [words.flatten] := by
  obtain ⟨word, rfl, _⟩ := List.map_eq_singleton_iff.mp hshape
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The streamed strict argmin and its greedy invariant. Candidate indices describe
an iterator's successive callbacks; no list of candidates is constructed here.
The finite-program implementation must refine these recurrences. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy

open OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect
open scoped BigOperators

variable {R X : Type*}


private theorem best_append (evaluate : R → ℕ) (seed : R) (xs ys : List R) :
    best evaluate seed (xs ++ ys) = best evaluate (best evaluate seed xs) ys := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- The native iterator's proof-only visit log agrees with the indexed scan.
The seed's repeated visit at index zero leaves its cached score unchanged. -/
theorem scan_eq_best (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).1 =
      best evaluate (candidate 0) ((List.range' 0 (t + 1)).map candidate) := by
  induction t with
  | zero => simp [scan, best]
  | succ t ih =>
    rw [List.range'_concat, List.map_append, best_append]
    simp only [Nat.one_mul, Nat.zero_add, List.map_cons, List.map_nil, best, ← ih]
    simp only [scan, update, scan_score]
    split_ifs <;> rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgminBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bootstrap the binary argmin from an empty incumbent. The initial candidate
load is paid explicitly, including the empty-input case. -/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem installFirst_eval (B C : ℕ) (next : Entry) (queue : List Bool)
    (regs : Fin 8 → Bool) (hn : Fits B C next) :
    ∃ n ≤ 100 * (B + C + 1), ∃ regs',
      Eval installFirst n (data regs next empty queue) (data regs' empty next queue) := by
  let d := data regs next empty queue
  have hr := replace_eval d (by rfl)
  have hc := cleanup_eval (afterReplace d)
  have hf : afterCleanup (afterReplace d) =
      data (afterCleanup (afterReplace d)).regs empty next queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ afterReplace, afterClear, afterCopy,
        StackRoutines.clearStacks, StackRoutines.copyStacks, d, data, store, empty]
  refine ⟨9 * next.payload.length + 9 * next.score.length + 25, ?_,
    (afterCleanup (afterReplace d)).regs, ?_⟩
  · rcases hn with ⟨hs, hp⟩
    omega
  · rw [← hf]
    convert Eval.seq hr hc using 1
    all_goals try with_reducible_and_instances rfl
    simp [afterReplace, afterClear, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks, d, data, store, empty]
    omega

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem readCounter_eval {r s : ℕ} (p : LoopPorts r s) (a : State r s) :
    Eval (readCounter p) 1 a (readCounterState p a) := .base (.atom _ _)

theorem iter_succ_apply {α : Type*} (next : α → α) (n : ℕ) (x : α) :
    iter next (n + 1) x = next (iter next n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [iter] using ih (next x)

theorem rounds_eval_bounded {r s : ℕ} {α : Type*} (p : LoopPorts r s)
    (body : Cmd r s) (next : α → α) (invariant : ℕ → α → State r s → Prop)
    (cost limit : ℕ) (h : BoundedRoundSpec p body next invariant cost limit)
    (q : ℕ) (x : α) (depth : List Bool) (a : State r s)
    (hq : q + depth.length ≤ limit) (hi : invariant q x a)
    (hd : a.stacks p.counter = depth) :
    ∃ n ≤ roundsBudget cost depth.length, ∃ b,
      invariant (q + depth.length) (iter next depth.length x) b ∧
      b.stacks p.counter = [] ∧ b.regs p.present = false ∧ Eval (rounds p body) n a b := by
  induction depth generalizing q x a with
  | nil =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = [] := by simp [b, readCounterState, hd]
    have hf : b.regs p.present = false := by simp [b, readCounterState, hd, readRegs]
    refine ⟨2, by simp [roundsBudget], b, h.read q x a hi, hb, hf, ?_⟩
    exact Eval.seq (readCounter_eval p a) (Eval.while_false hf)
  | cons bit depth ih =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = depth := by simp [b, readCounterState, hd]
    have ht : b.regs p.present = true := by simp [b, readCounterState, hd, readRegs]
    obtain ⟨u, hu, c, hc, hcounter, hguard, he⟩ :=
      h.step q x b (by simp only [List.length_cons] at hq; omega) (h.read q x a hi) ht
    obtain ⟨t, ht', d, hi', hd', hf', he'⟩ := ih (q + 1) (next x) c
      (by simp only [List.length_cons] at hq; omega) hc (hcounter.trans hb)
    cases he' with
    | @seq first second n m a' b' c' hread hloop =>
      refine ⟨1 + (u + n + m + 1), ?_, d, ?_, hd', hf', ?_⟩
      · simp only [roundsBudget, List.length_cons] at ht' ⊢
        nlinarith
      · simpa only [iter, List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hi'
      · exact Eval.seq (readCounter_eval p a)
          (Eval.while_true ht (Eval.seq he hread) hloop)

end SubexponentialSAT.SqrtLog.HashSelectProgram

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

/-- Exact measured appending, with no retained candidate family. -/
theorem append_eval (a : State 8 10) :
    Eval appendWinner (5 * (a.stacks 2).length + 2 * (a.stacks 3).length + 10)
      a (appended a) := by
  let b := Subexp.TupleProgram.pushedState 9 0 false a
  let c := Subexp.TupleProgram.escapedState appendPorts b
  let d := Subexp.TupleProgram.pushedState 9 0 true c
  have h1 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) false a
  have h2 := Subexp.TupleProgram.escape_eval_state appendPorts b
  have h3 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) true c
  have h4 := Subexp.TupleProgram.clear_eval (3 : Fin 10) (0 : Fin 8) 1 d
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  · rfl
  · simp [b, c, d, appendPorts]
    omega
  · rfl

theorem appended_history (a : State 8 10) :
    (appended a).stacks 9 =
      true :: (Encoding.frame (a.stacks 2).reverse ++ a.stacks 9) := by
  simp [appended, StackRoutines.clearStacks, appendPorts, Subexp.TupleProgram.frame_eq_escaped,
    List.append_assoc]

theorem appended_frame (a : State 8 10) (i : Fin 10)
    (h2 : i ≠ 2) (h3 : i ≠ 3) (h9 : i ≠ 9) :
    (appended a).stacks i = a.stacks i := by
  simp [appended, StackRoutines.clearStacks, appendPorts, h2, h3, h9]

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

/-- Bootstrap pays the first full score and stores it by actual copying. -/
theorem install_eval (a : State 40 896) (B C : ℕ) (hc : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hn : BinaryArgmin.Fits B C (readEntry 768 769 a)) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ b,
      Eval install n a b ∧
      b.stacks = stored a (readEntry 768 769 a) := by
  have hb : readEntry 770 771 a = BinaryArgmin.empty := by
    simp [readEntry, BinaryArgmin.empty, hbp, hbs]
  obtain ⟨n, hn', rf, he⟩ := BinaryArgmin.installFirst_eval B C
    (readEntry 768 769 a) [] (fun i => a.regs (registers i)) hn
  have ht := compiled_halt_trace he 8 2
  have hp := projected_core a hc
  rw [hb] at hp
  rw [← hp] at ht
  refine ⟨n + 1, by omega, _,
    eval_call_from_state _ registers coreStacks a
      core.register_injective core.stack_injective ht, ?_⟩
  exact embed_core_stacks a hc rf _

/-- Serialize precisely one attained winner and clear its cached score. -/
theorem append_eval (a : State 40 896) :
    ∃ b, Eval append (5 * (a.stacks 770).length + 2 * (a.stacks 771).length + 11) a b ∧
      b.stacks = appendedStacks a := by
  let d := projectState registers historyStacks a
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective historyStacks := by decide
  have he := HashGreedyProgram.append_eval d
  have ht := compiled_halt_trace he 2 9
  refine ⟨embedState registers historyStacks a (appended d),
    eval_call_from_state appendProgram registers historyStacks a hr hs ht, ?_⟩
  have hout : (appended d).stacks =
      Function.update (Function.update (Function.update d.stacks 2 []) 3 []) 9
        (true :: (Encoding.frame (d.stacks 2).reverse ++ d.stacks 9)) := by
    funext i
    by_cases h2 : i = 2
    · subst i
      simp
    by_cases h3 : i = 3
    · subst i
      simp
    by_cases h9 : i = 9
    · subst i
      simp [appended_history]
    simp only [Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h9, appended_frame d i h2 h3 h9]
  change Function.extend historyStacks _ a.stacks = _
  rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs]
  have hf : Function.extend historyStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers historyStacks a hr hs)
  rw [hf]
  rfl

theorem resetGuard_eval (a : State 40 896) : Eval resetGuard 1 a (guardSet a) :=
  .base (.atom _ _)

/-- Measured composition uses the actual execution of each fixed stage.
This is deliberately an intermediate trace lemma, not a closed query service. -/
theorem round_eval_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np : ℕ)
    (ha : Eval (attempt mass) na a b)
    (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e) :
    Eval (round mass) (na + (ni + (ns + (np + 1)))) a (guardSet e) :=
  ha.seq (hi.seq (hs.seq (hp.seq (resetGuard_eval e))))

theorem round_cost_le (attemptCost scoreWidth payloadWidth na ni ns np : ℕ)
    (ha : na ≤ attemptCost)
    (hi : ni ≤ 100 * (scoreWidth + payloadWidth + 1) + 1)
    (hs : ns ≤ 2 ^ payloadWidth *
      (attemptCost + 100 * (scoreWidth + payloadWidth + 1) + 1 +
        7 * (2 * payloadWidth + 3) + 5) + 2)
    (hp : np ≤ 5 * payloadWidth + 2 * scoreWidth + 11) :
    na + (ni + (ns + (np + 1))) ≤ roundBudget attemptCost scoreWidth payloadWidth := by
  unfold roundBudget
  omega

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

/-- One complete fixed native round: paid seed, all candidate visits, native
comparison, one attained winner append, and charged outer flag restoration.
The mathematical range in the conclusion records the trace; it is not stored. -/
theorem round_minimum (mass : Cmd 40 896) (a : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hcounter : a.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : a.stacks 779 = [])
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ roundBudget attemptCost B C, ∃ b : State 40 896, ∃ winner : BinaryArgmin.Entry,
      Eval (round mass) n a b ∧
      b.stacks = Function.update a.stacks 777
        (true :: (Encoding.frame winner.payload.reverse ++ a.stacks 777)) ∧
      b.regs 9 = true ∧ BinaryArgmin.Fits B C winner ∧
      (∃ j < 2 ^ C, winner = entry j) ∧
      (∀ j < 2 ^ C, BinaryArgmin.value winner ≤ BinaryArgmin.value (entry j)) ∧
      winner = HashSelect.best BinaryArgmin.value (entry 0)
        ((List.range' 0 (2 ^ C)).map entry) := by
  have hpositive : 0 < 2 ^ C := pow_pos (by decide) _
  obtain ⟨na, hna, first, hea, hfirst⟩ := hattempt [List.replicate C false] a
    (by simp) (fun _ _ _ _ _ => rfl) hcounter hscratch
  have hfirst' : first.stacks = Function.update (Function.update a.stacks 768
      (entry 0).payload) 769 (entry 0).score := by
    simpa [CounterPrograms.value] using hfirst
  have hcore' : CoreClean first := by
    constructor <;> simp [hfirst', hcore.scratch772, hcore.scratch773,
      hcore.scratch774, hcore.scratch775, hcore.queue776]
  have hentry : readEntry 768 769 first = entry 0 := by simp [readEntry, hfirst']
  obtain ⟨ni, hni, seed, hei, hseed⟩ := NativeRound.install_eval first B C hcore'
    (by simp [hfirst', hbp]) (by simp [hfirst', hbs]) (by simpa only [hentry] using hfit 0 hpositive)
  have hseed' : seed.stacks = stored first (entry 0) := by simpa only [hentry] using hseed
  have hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      seed.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    by_cases h768 : i = 768
    · subst i
      simp [hseed', stored, h0]
    by_cases h769 : i = 769
    · subst i
      simp [hseed', stored, h1]
    simp [hseed', stored, hfirst', h768, h769, h770, h771]
  have hs0 : seed.stacks 768 = [] := by simp [hseed', stored]
  have hs1 : seed.stacks 769 = [] := by simp [hseed', stored]
  have hsCore : CoreClean seed := by
    constructor
    · rw [hframe 772 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hframe 773 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hframe 774 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hframe 775 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hframe 776 (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hsCounter : seed.stacks 778 = Encoding.encodeList id [List.replicate C false] := by
    simp [hseed', stored, hfirst', hcounter]
  have hsScratch : seed.stacks 779 = [] := by simp [hseed', stored, hfirst', hscratch]
  have hsEntry : readEntry 770 771 seed = entry 0 := by simp [readEntry, hseed', stored]
  obtain ⟨ns, hns, final, hes, hfinal, hfScratch, hfCounter, hmem, hmin, hbest⟩ :=
    scan_minimum mass seed B C attemptCost entry hs0 hs1 hsCore hsCounter hsScratch hsEntry hfit
      (fun words d hw hd hc hs => hattempt words d hw
        (fun i h770 h771 h778 h779 => (hd.frame i h770 h771 h778 h779).trans
          (hframe i h770 h771 h778 h779)) hc hs)
  obtain ⟨after, hep, hafter⟩ := NativeRound.append_eval final
  let winner := readEntry 770 771 final
  have hfinalFrame : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
      final.stacks i = a.stacks i := by
    intro i h770 h771 h778 h779
    exact (hfinal.frame i h770 h771 h778 h779).trans (hframe i h770 h771 h778 h779)
  have hp : 5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11 ≤
      5 * C + 2 * B + 11 := by
    have hfitFinal := hfinal.fits
    rcases hfitFinal with ⟨hs, hp⟩
    dsimp only [readEntry] at hs hp
    omega
  refine ⟨na + (ni + (ns + (5 * (final.stacks 770).length +
    2 * (final.stacks 771).length + 11 + 1))),
    round_cost_le attemptCost B C _ _ _ _ hna hni hns hp,
    guardSet after, winner, ?_, ?_, by simp [guardSet], hfinal.fits, hmem, hmin, hbest⟩
  · exact round_eval_of_stages mass a first seed final after na ni ns
      (5 * (final.stacks 770).length + 2 * (final.stacks 771).length + 11) hea hei hes hep
  · change after.stacks = _
    rw [hafter]
    funext i
    by_cases h770 : i = 770
    · subst i
      simp [appendedStacks, hbp]
    by_cases h771 : i = 771
    · subst i
      simp [appendedStacks, hbs]
    by_cases h777 : i = 777
    · subst i
      simp [appendedStacks, winner, readEntry,
        hfinalFrame 777 (by decide) (by decide) (by decide) (by decide)]
    by_cases h778 : i = 778
    · subst i
      simp [appendedStacks, hfCounter, hcounter]
    by_cases h779 : i = 779
    · subst i
      simp [appendedStacks, hfScratch, hscratch]
    simp [appendedStacks, h770, h771, h777,
      hfinalFrame i h770 h771 h778 h779]

theorem chosenEntry_eq_best (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    chosenEntry entry C rows = HashSelect.best BinaryArgmin.value (entry rows 0)
      ((List.range' 0 (2 ^ C)).map (entry rows)) := by
  have hp : 1 ≤ 2 ^ C := by have := pow_pos (by decide : 0 < (2 : ℕ)) C; omega
  simpa only [chosenEntry, Nat.sub_add_cancel hp] using
    HashGreedy.scan_eq_best BinaryArgmin.value (entry rows) (2 ^ C - 1)

theorem rowBoundary_read (base a : State 40 896) (rows : List (List Bool))
    (ha : RowBoundary base rows a) :
    RowBoundary base rows (HashSelectProgram.readCounterState outer a) := by
  constructor
  · intro i h777 h781
    simpa [HashSelectProgram.readCounterState, outer, h781] using ha.frame i h777 h781
  · simpa [HashSelectProgram.readCounterState, outer] using ha.history

theorem rowBoundary_round (base a b : State 40 896) (rows : List (List Bool))
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (C : ℕ)
    (ha : RowBoundary base rows a)
    (hb : b.stacks = Function.update a.stacks 777
      (true :: (Encoding.frame (chosenEntry entry C rows).payload.reverse ++ a.stacks 777))) :
    RowBoundary base (nextRows entry C rows) b := by
  constructor
  · intro i h777 h781
    simpa [hb, h777] using ha.frame i h777 h781
  · simp [hb, ha.history, encodedHistory, nextRows, Encoding.encodeList]

/-- Actual unary-controlled iteration of complete native rounds, with literal
history serialization and exact caller-frame preservation. The query cost is
needed only at the bounded histories that this execution can reach. -/
theorem rounds_history (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = count)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = [])
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j))
    (hattempt : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry rows (CounterPrograms.value words.flatten)).payload) 769
          (entry rows (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ HashSelectProgram.roundsBudget (roundBudget attemptCost B C) count, ∃ b,
      Eval (NativeRound.rounds mass) n base b ∧
      RowBoundary base (HashSelectProgram.iter (nextRows entry C) count initial) b ∧
      b.stacks 781 = [] ∧ b.regs 9 = false := by
  let invariant := fun q rows a => RowBoundary base rows a ∧ rows.length = initial.length + q ∧
    rows = HashSelectProgram.iter (nextRows entry C) q initial ∧
    (encodedHistory rows).length ≤ (encodedHistory initial).length + q * (2 * C + 2)
  have spec : HashSelectProgram.BoundedRoundSpec outer (round mass) (nextRows entry C)
      invariant (roundBudget attemptCost B C) count := by
    constructor
    · intro q rows a ha
      exact ⟨rowBoundary_read base a rows ha.1, ha.2⟩
    · intro q rows a hq ha hflag
      have hlen : rows.length ≤ initial.length + count := by
        have hh := ha.2.1
        omega
      have hbytes : (encodedHistory rows).length ≤
          (encodedHistory initial).length + count * (2 * C + 2) :=
        ha.2.2.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hq.le) _)
      have hf := ha.1.frame
      have hcoreA : CoreClean a := by
        constructor
        · rw [hf 772 (by decide) (by decide)]
          exact hcore.scratch772
        · rw [hf 773 (by decide) (by decide)]
          exact hcore.scratch773
        · rw [hf 774 (by decide) (by decide)]
          exact hcore.scratch774
        · rw [hf 775 (by decide) (by decide)]
          exact hcore.scratch775
        · rw [hf 776 (by decide) (by decide)]
          exact hcore.queue776
      obtain ⟨n, hn, b, winner, he, hb, hguard, hwfit, _, _, hbest⟩ :=
        round_minimum mass a B C attemptCost (entry rows)
          ((hf 768 (by decide) (by decide)).trans h0)
          ((hf 769 (by decide) (by decide)).trans h1) hcoreA
          ((hf 770 (by decide) (by decide)).trans hbp)
          ((hf 771 (by decide) (by decide)).trans hbs)
          ((hf 778 (by decide) (by decide)).trans hcounter)
          ((hf 779 (by decide) (by decide)).trans hscratch)
          (hfit rows hlen) (hattempt rows a hlen ha.1 ⟨q,hq.le,ha.2.2.1⟩ hbytes)
      have hwinner : winner = chosenEntry entry C rows :=
        hbest.trans (chosenEntry_eq_best entry C rows).symm
      rw [hwinner] at hb
      refine ⟨n, hn, b, ⟨rowBoundary_round base a b rows entry C ha.1 hb, ?_, ?_, ?_⟩,
        ?_, hguard, he⟩
      · dsimp only [nextRows]
        simp only [List.length_cons, ha.2.1]
        omega
      · rw [HashSelectProgram.iter_succ_apply, ← ha.2.2.1]
      · have hlenNext : (encodedHistory (nextRows entry C rows)).length =
            (encodedHistory rows).length + 2 * (chosenEntry entry C rows).payload.length + 2 := by
          simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
          omega
        rw [hlenNext, Nat.succ_mul q (2 * C + 2)]
        rw [hwinner] at hwfit
        have hh := ha.2.2.2
        have hw := hwfit.2
        omega
      · simp [hb, outer]
  have hi : invariant 0 initial base := ⟨⟨fun _ _ _ => rfl, hhistory⟩, by simp, rfl, by simp⟩
  obtain ⟨n, hn, b, hb, hcounter', hflag, he⟩ :=
    HashSelectProgram.rounds_eval_bounded outer (round mass) (nextRows entry C) invariant
      (roundBudget attemptCost B C) count spec 0 initial (base.stacks 781) base
      (by simp [hdepth]) hi rfl
  refine ⟨n, by simpa only [hdepth] using hn, b, he, ?_, hcounter', hflag⟩
  simpa only [hdepth] using hb.1

theorem chosenEntry_mem (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (rows : List (List Bool)) :
    ∃ j < 2 ^ C, chosenEntry entry C rows = entry rows j := by
  have hm := HashSelect.best_mem BinaryArgmin.value (entry rows 0)
    ((List.range' 0 (2 ^ C)).map (entry rows))
  rw [← chosenEntry_eq_best] at hm
  rcases List.mem_cons.mp hm with hzero | hrest
  · exact ⟨0, pow_pos (by decide) _, hzero⟩
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hrest
    exact ⟨j, by simpa using hj, he.symm⟩

theorem chosenEntry_fits (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (B C : ℕ) (rows : List (List Bool))
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    BinaryArgmin.Fits B C (chosenEntry entry C rows) := by
  obtain ⟨j, hj, he⟩ := chosenEntry_mem entry C rows
  rw [he]
  exact hfit j hj

theorem iter_length (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (C : ℕ) (initial : List (List Bool)) (q : ℕ) :
    (HashSelectProgram.iter (nextRows entry C) q initial).length = initial.length + q := by
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    rw [HashSelectProgram.iter_succ_apply]
    simp [nextRows, ih, Nat.add_assoc]

/-- The physical serialized history grows only by the selected bounded row.
The exponentially many losing payloads never contribute to this retained word. -/
theorem encodedHistory_iter_length_le
    (entry : List (List Bool) → ℕ → BinaryArgmin.Entry) (B C count : ℕ)
    (initial : List (List Bool))
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j)) :
    ∀ q ≤ count,
      (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length ≤
        (encodedHistory initial).length + q * (2 * C + 2) := by
  intro q
  induction q with
  | zero => simp [HashSelectProgram.iter]
  | succ q ih =>
    intro hq
    have hi := ih (by omega)
    have hfitChosen := chosenEntry_fits entry B C
      (HashSelectProgram.iter (nextRows entry C) q initial)
      (hfit _ (by rw [iter_length]; omega))
    have hbytes := hfitChosen.2
    rw [HashSelectProgram.iter_succ_apply]
    have hlen : (encodedHistory (nextRows entry C
        (HashSelectProgram.iter (nextRows entry C) q initial))).length =
        (encodedHistory (HashSelectProgram.iter (nextRows entry C) q initial)).length +
          2 * (chosenEntry entry C (HashSelectProgram.iter (nextRows entry C) q initial)).payload.length + 2 := by
      simp [encodedHistory, nextRows, Encoding.encodeList, Encoding.length_frame]
      omega
    rw [hlen, Nat.succ_mul q (2 * C + 2)]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem entry_fits {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ) :
    BinaryArgmin.Fits (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)
      (entry rowAccept weight n m depth rows rank) := by
  constructor <;> simp [entry]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CNF scores instantiate the actual unary-controlled greedy run.
The only execution seam is the actual per-mark query. Initial-code distance
is used only for the final zero-mass and exact model-set consequences. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem staged_rounds_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = HashSelect.loopCap n m)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hcounter : base.stacks 778 = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false])
    (hs : base.stacks 779 = [])
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ HashSelectProgram.roundsBudget
      (roundBudget (stagedAttemptBudget base n m depth queryCost L)
        (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)) (HashSelect.loopCap n m),
      ∃ b, Eval (NativeRound.rounds (HashMassStaged.command query)) t base b ∧
        RowBoundary base (HashGreedyCNF.history clauses depth initial (HashSelect.loopCap n m)) b ∧
        b.stacks 781 = [] ∧ b.regs 9 = false := by
  apply rounds_history (HashMassStaged.command query) base (HashSelect.loopCap n m)
    (HashCandidates.payloadWidth m depth) (stagedAttemptBudget base n m depth queryCost L)
    (HashSelect.loopCap n m) (HashGreedyCNF.entry clauses depth) initial
    hhistory hdepth h0 h1 hcore hbp hbs hcounter hs
  · intro rows _ rank _
    exact HashGreedyCandidate.entry_fits _ _ n m depth rows rank
  intro rows a hrows ha hactual hbytes words d hwords hd hcounterD hsD
  apply staged_boundary_attempt clauses hm query queryCost base h0 h1 hcore hlow ht
    hwidth hvalue hmword hshape hcollector L hsource hC hempty rows a ha
    (hbytes.trans hbytesL) words d hwords hd hcounterD hsD
  have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
    have hh := congrArg List.sum hwords
    simpa [List.length_flatten] using hh
  have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
  have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i := by
    intro i h770 h771 h777 h778 h779 h781
    exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
  exact hq rows words.flatten d hrows hactual hbytes hword hf
    ((hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history)
    (hcounterD.trans (congrArg (Encoding.encodeList id) hsingle)) hsD

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyStagedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix storage for the physically staged candidate attempt. The full marked-query
runtime never appears in this bound: the marked queries supply an independent
prefix cap, while preparation, reference setup and padding are polynomial. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashGreedyExecution

theorem attemptSpace_congr (a b : State 40 896) (n m depth L K : ℕ)
    (h0 : a.stacks 0 = b.stacks 0) (h782 : a.stacks 782 = b.stacks 782) :
    attemptSpace a n m depth L K = attemptSpace b n m depth L K := by
  simp only [attemptSpace, LeafOuterProgram.routeCost, h0, h782]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRunSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform source-prefix storage for the actual physically staged greedy run.
The caller and attained-history bounds are maintained by the actual loops;
the expensive marked query contributes only its independent prefix cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRunSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

private theorem loader_clean (a : State 40 896)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hs : a.stacks 779 = []) :
    ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [] := by
  rcases hcore with ⟨h2,h3,h4,h5,h6⟩
  intro j hj2 hj3 hj9
  fin_cases j <;> simp_all [HashCandidateProgram.Leaf.loaderStacks]

theorem boundary_attempt_space {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
    (base : State 40 896)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = []) (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (L K : ℕ) (hC : HashCandidates.payloadWidth m depth ≤ L) (hB : HashSelect.loopCap n m ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (rows : List (List Bool)) (word : List Bool) (d : State 40 896)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hcounterD : d.stacks 778 = Encoding.encodeList id [word]) (hsD : d.stacks 779 = [])
    (hdL : ∀ i, (d.stacks i).length ≤ L)
    (hq : ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun ws => ws = workspace
        (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896}
    (he : Eval (attempt (HashMassStaged.command query)) steps d result) :
    StageSpace (attempt (HashMassStaged.command query)) (steps + 1) d
      (HashGreedyStagedSpace.attemptSpace base n m depth L K) := by
  have hcoreD : CoreClean d := by
    constructor
    · rw [hf 772 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hf 773 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hf 774 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hf 775 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hf 776 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hlowD : ∀ i : Fin 896, i.val < 12 → d.stacks i = [] := by
    intro i hi
    have hneq (j : Fin 896) (hj : 12 ≤ j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hlow i hi
  have hcD : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → d.stacks i = [] := by
    intro i hi hj
    have hneq (j : Fin 896) (hj : 324 < j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hcollector i hi hj
  have hemptyD : ∀ i ∈ HashMassStaged.stagedPorts, d.stacks i = [] := by
    intro i hi
    have hsmall : i.val < 770 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hneq (j : Fin 896) (hj : 770 ≤ j.val) : i ≠ j := by intro h; subst i; omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hempty i hi
  have h := HashGreedyStagedSpace.attempt_halt_space clauses hm rows query queryCost d word L K
    hdL hC hB href hgrowth hword hcounterD
    (loader_clean d
      ((hf 768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
      hcoreD hsD) hlowD
    (by rw [hf 767 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvalue)
    (by rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmword)
    (by rw [hf 818 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hshape)
    hcD hemptyD hq hspace he
  rw [HashGreedyStagedSpace.attemptSpace_congr d base n m depth L K
    (hf 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))] at h
  exact h

theorem rounds_halt_space {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = HashSelect.loopCap n m)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hcounter : base.stacks 778 = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false])
    (hs : base.stacks 779 = [])
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : HashSelect.loopCap n m ≤ L)
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
      ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896}
    (he : Eval (NativeRound.rounds (HashMassStaged.command query)) steps base result) :
    StageSpace (NativeRound.rounds (HashMassStaged.command query)) (steps + 1) base
      (max (HashGreedyStagedSpace.attemptSpace base n m depth L K)
        (896 * L + 100 * (HashSelect.loopCap n m + HashCandidates.payloadWidth m depth + 1) +
          7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20)) := by
  apply HashGreedyScanSpace.rounds_halt_space (HashMassStaged.command query) base
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) L
    (HashGreedyStagedSpace.attemptSpace base n m depth L K)
    (stagedAttemptBudget base n m depth queryCost L) (HashSelect.loopCap n m)
    (HashGreedyCNF.entry clauses depth) initial hhistory hdepth h0 h1 hcore hbp hbs
    hbase hB hC hcounterBound hbytesL hcounter hs
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) ?_ ?_ he
  · intro rows a hrows ha hactual hbytes words d hwords hd hc hsD
    apply HashGreedyRun.staged_boundary_attempt clauses hm query queryCost base h0 h1 hcore hlow ht
      hwidth hvalue hmword hshape hcollector L (fun i _ => hbase i) hC hempty rows a ha
      (hbytes.trans hbytesL) words d hwords hd hc hsD
    have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
      have hh := congrArg List.sum hwords
      simpa [List.length_flatten] using hh
    have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
    have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i := by
      intro i h770 h771 h777 h778 h779 h781
      exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
    exact hq rows words.flatten d hrows hactual hbytes hword hf
      ((hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history)
      (hc.trans (congrArg (Encoding.encodeList id) hsingle)) hsD
  · intro rows a hrows ha hactual hbytes words d t b hwords hd hc hsD hdL htD
    have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
      have hh := congrArg List.sum hwords
      simpa [List.length_flatten] using hh
    have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
    have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i := by
      intro i h770 h771 h777 h778 h779 h781
      exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
    have hhist : d.stacks 777 = encodedHistory rows :=
      (hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history
    have hcounterD : d.stacks 778 = Encoding.encodeList id [words.flatten] :=
      hc.trans (congrArg (Encoding.encodeList id) hsingle)
    have hbound := boundary_attempt_space clauses hm query queryCost base h0 h1 hcore hlow ht
      hwidth hvalue hmword hshape hcollector hempty L K hC hB href hgrowth rows words.flatten d
      hword hf hcounterD hsD hdL
      (hq rows words.flatten d hrows hactual hbytes hword hf hhist hcounterD hsD)
      (hspace rows words.flatten d hrows hactual hbytes hword hf hhist hcounterD hsD hdL) htD
    constructor
    intro k c hk hc'
    exact hbound.bound k c (by omega) hc'

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRunSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF HashGreedyCode

theorem history_bytes {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    (encodedHistory (history clauses depth start rounds)).length ≤
      (encodedHistory start).length + rounds * (2 * HashCandidates.payloadWidth m depth + 2) := by
  exact HashGreedyRound.encodedHistory_iter_length_le (entry clauses depth)
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) rounds start
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) rounds le_rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem ready_low {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] :=
  NativeCodeAssembly.worker_empty a hr.worker

theorem ready_core {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) : CoreClean a := by
  constructor
  · exact hr.core 772 (by decide)
  · exact hr.core 773 (by decide)
  · exact hr.core 774 (by decide)
  · exact hr.core 775 (by decide)
  · exact hr.core 776 (by decide)

theorem ready_staging {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [] := by
  intro i hi
  apply ready_low hr i
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Physical readiness is supplied by the actual preparation theorem. The
execution and resource theorem use the identical staged attempt budget L. -/
theorem ready_rounds_oai {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (depth : ℕ)
    (hd : depth = SparseCode.distanceDenom m B) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : HashSelect.loopCap n m ≤ L)
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
      ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    : ∃ steps out, steps ≤ roundsTime base n m depth queryCost L ∧
      Eval (roundsCommand query) steps base out ∧
      RowBoundary base (HashGreedyCNF.history clauses depth
        initial (HashSelect.loopCap n m)) out ∧
      out.stacks 781 = [] ∧ out.regs 9 = false ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      StageSpace (roundsCommand query) (steps + 1) base (roundsSpace base n m depth L K) := by
  have hcounter : base.stacks 778 = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false] := by
    rw [hd]
    exact hr.counter
  have hlo := ready_low hr
  have h0 := hr.core 768 (by decide)
  have h1 := hr.core 769 (by decide)
  have hbp := hr.core 770 (by decide)
  have hbs := hr.core 771 (by decide)
  have hcore := ready_core hr
  have hrounds : (base.stacks 781).length = HashSelect.loopCap n m := by
    simp only [hr.rounds, List.length_replicate]
  have hshape : (base.stacks 818).length = HashSelect.loopCap n m := by
    simp only [hr.shape, List.length_replicate]
  have hmw : CounterPrograms.value (base.stacks 782) = m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.clauses
  have hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [] := by
    intro i hi
    exact hlo i (by omega)
  have hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [] := by
    intro i _ hi
    exact hlo i (by omega)
  obtain ⟨steps,ht,out,he,hout,h781,h9⟩ := HashGreedyRun.staged_rounds_eval clauses hm
    initial query queryCost base hr.history hrounds h0 h1 hcore hbp hbs
    hcounter hr.scratch hlow (hlo 767 (by decide)) hr.modulus_length hr.modulus hmw hshape
    hcollector L (fun i _ => hbase i) hC hbytesL (ready_staging hr) hq
  have hs := HashGreedyRunSpace.rounds_halt_space clauses hm initial
    query queryCost base hr.history hrounds h0 h1 hcore hbp hbs hcounter hr.scratch hlow
    (hlo 767 (by decide)) hr.modulus_length hr.modulus hmw hshape hcollector L K hbase hB
    hcounterBound href hgrowth hC hbytesL (ready_staging hr) hq hspace he
  refine ⟨steps,out,ht,he,hout,h781,h9,?_,hs⟩
  intro i
  by_cases h777 : i = 777
  · subst i
    rw [hout.history]
    exact (HashQueryInputBounds.history_bytes clauses depth
      initial (HashSelect.loopCap n m)).trans hbytesL
  by_cases h781' : i = 781
  · subst i
    simp only [h781, List.length_nil, Nat.zero_le]
  rw [hout.frame i h777 h781']
  exact hbase i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds_oai
