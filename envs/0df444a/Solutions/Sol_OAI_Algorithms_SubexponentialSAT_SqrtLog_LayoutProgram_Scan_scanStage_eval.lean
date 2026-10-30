-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:01:23.980172+00:00
-- url     : https://prove2.me/submissions/96dface1-b022-4cd8-a927-2516a0156152

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S081
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixInputTypes_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixScanStepProgram_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

theorem popCount_eval (a : Data) : Eval popCount 1 a (popped a) := .base (.atom _ _)

theorem output_stack_frame (a : Data) (w rests : ColorRow) (j : Fin 23)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (hout : j.val < 13 ∨ 21 ≤ j.val) :
    (MatrixScanStepProgram.output a w rests).stacks j = a.stacks j := by
  fin_cases j <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, clearStacks] at *

theorem output_targets (a : Data) (w rests : ColorRow) (i : Fin 4) :
    (MatrixScanStepProgram.output a w rests).stacks (MatrixColorReadProgram.target i) = [] := by
  fin_cases i <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixColorReadProgram.target, clearStacks]

theorem output_sources (a : Data) (w rests : ColorRow) (i : Fin 4) :
    (MatrixScanStepProgram.output a w rests).stacks (MatrixColorReadProgram.source i) = rests i := by
  fin_cases i <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts, MatrixColorReadProgram.source, clearStacks]

theorem output_ready (a : Data) (w : ColorRow) (ws : List ColorRow) (width : ℕ)
    (h : Ready a (w :: ws) width) :
    Ready (MatrixScanStepProgram.output (popped a) w (streams ws)) ws width := by
  constructor
  · rw [output_stack_frame _ _ _ 0 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero0
  · rw [output_stack_frame _ _ _ 1 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero1
  · rw [output_stack_frame _ _ _ 4 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero4
  · rw [output_stack_frame _ _ _ 10 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero10
  · rw [output_stack_frame _ _ _ 11 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero11
  · rw [output_stack_frame _ _ _ 12 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero12
  · exact output_targets _ _ _
  · exact output_sources _ _ _
  · rw [output_stack_frame _ _ _ 21 (by decide) (by decide) (by decide)]
    simpa [popped] using h.width_length
  · rw [output_stack_frame _ _ _ 22 (by decide) (by decide) (by decide)]
    simp only [popped, Function.update_same, List.length_tail]
    rw [h.count_length]
    simp
  · intro v hv i
    exact h.row_length v (List.mem_cons_of_mem w hv) i

theorem popped_guard (a : Data) :
    (popped a).regs 6 = !(a.stacks 22).isEmpty := by
  cases he : a.stacks 22 <;> simp [popped, readRegs, he]

private theorem target_ne_count (i : Fin 4) : MatrixColorReadProgram.target i ≠ 22 := by
  intro h
  have hv := congrArg (fun j : Fin 23 => j.val) h
  change 13 + i.val = 22 at hv
  omega

private theorem source_ne_count (i : Fin 4) : MatrixColorReadProgram.source i ≠ 22 := by
  intro h
  have hv := congrArg (fun j : Fin 23 => j.val) h
  change 17 + i.val = 22 at hv
  omega

theorem loop_eval (a : Data) (rows : List ColorRow) (width : ℕ) (h : Ready a rows width) :
    ∃ n ≤ rows.length * (208 * width + 149) + 1,
      Eval loop n (popped a) (result rows a) := by
  induction rows generalizing a with
  | nil =>
      have hz : a.stacks 22 = [] := List.length_eq_zero_iff.mp h.count_length
      have hg : (popped a).regs 6 = false := by simp [popped_guard, hz]
      exact ⟨1, by simp, Eval.while_false hg⟩
  | cons w ws ih =>
      have hg : (popped a).regs 6 = true := by
        rw [popped_guard]
        have hp : (a.stacks 22).length > 0 := by rw [h.count_length]; simp
        cases he : a.stacks 22 with
        | nil => simp [he] at hp
        | cons bit tail => rfl
      obtain ⟨ns, hns, hs⟩ := MatrixScanStepProgram.command_eval (popped a) w (streams ws)
        (by simpa [popped] using h.zero0) (by simpa [popped] using h.zero1)
        (by simpa [popped] using h.zero4) (by simpa [popped] using h.zero10)
        (by simpa [popped] using h.zero11) (by simpa [popped] using h.zero12)
        (by intro i; simpa [popped, target_ne_count i] using h.targets i)
        (by intro i; simpa [popped, source_ne_count i] using h.sources i)
        (by intro i; simpa [popped, h.width_length] using h.row_length w (by simp) i)
      let next := MatrixScanStepProgram.output (popped a) w (streams ws)
      have hp := popCount_eval next
      obtain ⟨nt, hnt, ht⟩ := ih next (output_ready a w ws width h)
      refine ⟨(ns + 1) + nt + 1, ?_, Eval.while_true hg (hs.seq hp) ht⟩
      have hw : ((popped a).stacks 21).length = width := by simpa [popped] using h.width_length
      rw [hw] at hns
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem program_runsIn (a : Data) (rows : List ColorRow) (width : ℕ) (h : Ready a rows width) :
    RunsIn program (rows.length * (208 * width + 149) + 3)
      (a.withPC (some program.entry)) ((result rows a).withPC none) := by
  obtain ⟨n, hn, ht⟩ := loop_eval a rows width h
  exact ⟨1 + n + 1, by omega, compiled_halt_trace ((popCount_eval a).seq ht) 17 2⟩

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

theorem output_count2 (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).stacks 2 =
      if same w && !swapped w then true :: a.stacks 2 else a.stacks 2 := by
  simp +decide [same, swapped, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, clearStacks]

theorem output_count3 (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).stacks 3 =
      if swapped w && !same w then true :: a.stacks 3 else a.stacks 3 := by
  simp +decide [same, swapped, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, clearStacks]

theorem output_compatible (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).regs 7 = (a.regs 7 && compatible w) := by
  simp +decide [same, swapped, compatible, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, readRegs]

theorem result_count2 (rows : List ColorRow) (a : Data) :
    (result rows a).stacks 2 = List.replicate (unchangedCount rows) true ++ a.stacks 2 := by
  induction rows generalizing a with
  | nil => simp [result, unchangedCount, popped]
  | cons w ws ih =>
      rw [result, ih, output_count2]
      simp only [popped, Function.update_of_ne (by decide : (2 : Fin 23) ≠ 22)]
      cases he : same w && !swapped w <;>
        simp [unchangedCount, he, List.replicate_add, List.append_assoc]

theorem result_count3 (rows : List ColorRow) (a : Data) :
    (result rows a).stacks 3 = List.replicate (transposedCount rows) true ++ a.stacks 3 := by
  induction rows generalizing a with
  | nil => simp [result, transposedCount, popped]
  | cons w ws ih =>
      rw [result, ih, output_count3]
      simp only [popped, Function.update_of_ne (by decide : (3 : Fin 23) ≠ 22)]
      cases he : swapped w && !same w <;>
        simp [transposedCount, he, List.replicate_add, List.append_assoc]

theorem result_compatible (rows : List ColorRow) (a : Data) :
    (result rows a).regs 7 = (a.regs 7 && rows.all compatible) := by
  induction rows generalizing a with
  | nil => simp [result, popped, readRegs]
  | cons w ws ih =>
      rw [result, ih, output_compatible]
      simp [popped, readRegs, Bool.and_assoc]

theorem result_stack_frame (rows : List ColorRow) (a : Data) (j : Fin 23)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (h22 : j ≠ 22)
    (hout : j.val < 13 ∨ 21 ≤ j.val) :
    (result rows a).stacks j = a.stacks j := by
  induction rows generalizing a with
  | nil => simp [result, popped, h22]
  | cons w ws ih =>
      rw [result, ih, output_stack_frame _ _ _ j h2 h3 hout]
      simp [popped, h22]

theorem result_targets (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) (i : Fin 4) :
    (result rows a).stacks (MatrixColorReadProgram.target i) = [] := by
  induction rows generalizing a with
  | nil =>
      have ht := h.targets i
      fin_cases i <;> simpa [result, popped, MatrixColorReadProgram.target] using ht
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

theorem result_sources (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) (i : Fin 4) :
    (result rows a).stacks (MatrixColorReadProgram.source i) = [] := by
  induction rows generalizing a with
  | nil =>
      have hs := h.sources i
      fin_cases i <;> simpa [result, popped, MatrixColorReadProgram.source] using hs
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

theorem result_counter (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) : (result rows a).stacks 22 = [] := by
  induction rows generalizing a with
  | nil =>
      have hz : a.stacks 22 = [] := List.length_eq_zero_iff.mp h.count_length
      simp [result, popped, hz]
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

theorem result_stacks (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) : (result rows a).stacks = resultStacks rows a := by
  funext j
  fin_cases j
  · simpa [resultStacks] using result_stack_frame rows a 0 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 1 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_count2 rows a
  · simpa [resultStacks] using result_count3 rows a
  · simpa [resultStacks] using result_stack_frame rows a 4 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 5 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 6 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 7 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 8 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 9 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 10 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 11 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 12 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 0
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 1
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 2
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 3
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 0
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 1
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 2
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 3
  · simpa [resultStacks] using result_stack_frame rows a 21 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_counter rows a width h

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem rows_width (i : Fin Δ) (u y : UniversalType r Q Δ) :
    ∀ w ∈ rows i u y, ∀ j, (w j).length = r := by
  intro w hw j
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hw
  exact typedRow_length i u y l j

theorem rows_streams (i : Fin Δ) (u y : UniversalType r Q Δ) :
    streams (rows i u y) =
      ![ReadPlan.encodeWord u.head, ReadPlan.encodeWord (u.slot i),
        ReadPlan.encodeWord y.head, ReadPlan.encodeWord (y.slot i)] := by
  funext j
  fin_cases j <;> simp [streams, rows, Function.comp_def, typedRow, encodeColor, ReadPlan.encodeWord]

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port execution rules used to assemble the concrete entry program.
The call rule consumes a trace of the supplied actual subprogram. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

theorem lowRegisters_injective : Function.Injective lowRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 9 => k.val) h

theorem lowStacks_injective {s : ℕ} (hs : s ≤ 37) :
    Function.Injective (Fin.castLE hs) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 37 => k.val) h

theorem embed_install {s : ℕ} (hs : s ≤ 37) (a : Data) (b : State 8 s) :
    embedState lowRegisters (Fin.castLE hs) a b = install a b := by
  apply embedState_eq_of_ports _ _ _ _ _ lowRegisters_injective (lowStacks_injective hs)
  · intro j
    simp [install, lowRegisters, j.isLt]
  · intro j hj
    have hn : ¬ j.val < 8 := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]
  · intro j
    simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < s := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]

theorem install_project {s : ℕ} (hs : s ≤ 37) (a : Data) :
    install a (project hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : j.val < 8 <;> simp [ project, lowRegisters, h]
  · funext j
    by_cases h : j.val < s <;> simp [ project, h]

theorem callLow_eval {s l : ℕ} (p : Program 8 s l) (hs : s ≤ 37)
    (a : Data) (b : State 8 s) {n : ℕ}
    (ht : Trace p n ((project hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (callLow p hs) n a (install a b) := by
  have he := eval_call_lifted p lowRegisters (Fin.castLE hs) a
    lowRegisters_injective (lowStacks_injective hs) ht
  rw [embed_install, embed_install, install_project] at he
  exact he

theorem copy_eval (a : Data) (src dst : Fin 37)
    (hsd : src ≠ dst) (hs9 : src ≠ 9) (h9d : (9 : Fin 37) ≠ dst) (h9 : a.stacks 9 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 9 (0 : Fin 9) 1 hsd hs9 h9d (by decide) a h9

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual type-byte extractor and color classifier with arbitrary retained
integer caches. No finite-field arithmetic is called by this stage. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Scan

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

variable {r Q Δ : ℕ}

theorem scanStage_eval_oai (i : Fin Δ) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) :
    ∃ n ≤ scanStageCost r Q Δ i.val, ∃ out,
      Eval scanStage n (scanInput i u y cache0 cache1 cache2 cache3 regs)
        (counted (scanInput i u y cache0 cache1 cache2 cache3 regs) out
          (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y))
          (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y))) ∧
      out 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
        (MatrixEntryEvaluation.rows i u y).all MatrixScanProgram.compatible) := by
  let base := scanInput i u y cache0 cache1 cache2 cache3 regs
  let a1 := copied base 22 33
  let localRegs : Fin 8 → Bool := fun j => a1.regs (lowRegisters j)
  let a2 := install a1 (MatrixInputTypes.output i u y localRegs)
  let inner := project (by decide : 23 ≤ 37) a2
  let rows := MatrixEntryEvaluation.rows i u y
  let a3 := install a2 (MatrixScanProgram.result rows inner)
  have t0 := copy_eval base 22 33 (by decide) (by decide) (by decide)
    (by simp [base, scanInput, input])
  have hin : project (by decide : 29 ≤ 37) a1 = MatrixInputTypes.input i u y localRegs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [ a1, copied, copyStacks, base, scanInput, input
]
  obtain ⟨ni, hni, hi⟩ := MatrixInputTypes.program_runsIn i u y localRegs
  rw [← hin] at hi
  have t1 := callLow_eval MatrixInputProgram.program (by decide) a1
    (MatrixInputTypes.output i u y localRegs) hi
  have hready : MatrixScanProgram.Ready inner rows r := by
    constructor
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · intro j
      fin_cases j <;>
        simp +decide [inner, project, a2, install, MatrixColorReadProgram.target,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · intro j
      rw [show MatrixScanProgram.streams rows =
          ![ReadPlan.encodeWord u.head, ReadPlan.encodeWord (u.slot i),
            ReadPlan.encodeWord y.head, ReadPlan.encodeWord (y.slot i)] from
              MatrixEntryEvaluation.rows_streams i u y]
      fin_cases j <;>
        simp +decide [inner, project, a2, install, MatrixColorReadProgram.source,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState, rows]
    · exact MatrixEntryEvaluation.rows_width i u y
  obtain ⟨ns, hns, hs⟩ := MatrixScanProgram.program_runsIn inner rows r hready
  have t2 := callLow_eval MatrixScanProgram.program (by decide) a2
    (MatrixScanProgram.result rows inner) hs
  have hstacks := MatrixScanProgram.result_stacks rows inner r hready
  have hend : a3 = counted base a3.regs
      (MatrixScanProgram.unchangedCount rows) (MatrixScanProgram.transposedCount rows) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      simp only [ hstacks]
      fin_cases j <;>
        simp +decide [ MatrixScanProgram.resultStacks, inner, project, a2, install,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState,
          a1, copied, copyStacks, base, scanInput, input]
  have hflag : a3.regs 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
      rows.all MatrixScanProgram.compatible) := by
    have h7 : a3.regs 7 = (MatrixScanProgram.result rows inner).regs 7 := rfl
    rw [h7, MatrixScanProgram.result_compatible]
    simp +decide [inner, project, a2, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixEntryKernel.SpectatorsAgree]
  have he := t0.seq (t1.seq (t2.seq (Eval.base (StructuredProgram.Eval.skip a3))))
  rw [hend] at he
  refine ⟨(7 * Q + 5) + (ni + (ns + 0)), ?_, a3.regs, ?_, hflag⟩
  · simp only [rows, MatrixEntryEvaluation.rows_length] at hns
    dsimp [scanStageCost]
    omega
  · simpa [scanStage, series, base, scanInput, input] using he

end SubexponentialSAT.SqrtLog.LayoutProgram.Scan

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval_oai
