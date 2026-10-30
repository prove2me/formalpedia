-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:10:49.708991+00:00
-- url     : https://prove2.me/submissions/d9232be1-19de-4eed-be22-dfbf61cd1891

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S074
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S097

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixColorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed program that consumes one color word from each of the four
matrix-input streams. The word width is supplied as a unary stack. -/

namespace SubexponentialSAT.Subexp.MatrixColorReadProgram

open BitProgram StructuredCalls StackRoutines ArrayPrograms

theorem copyWidth_eval (a : Data) (h0 : a.stacks 0 = []) :
    Eval copyWidth (7 * (a.stacks 21).length + 5) a (copiedWidth a) :=
  TupleProgram.copy_eval 21 10 0 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h0

theorem take_eval (a : Data) (src : Fin 23) (segment rest : List Bool)
    (h10 : (10 : Fin 23) ≠ src) (h4 : src ≠ 4)
    (hs : a.stacks src = segment ++ rest)
    (hlen : (a.stacks 10).length = segment.length) :
    Eval (take src) (4 * segment.length + 3) a (taken a src segment rest) := by
  have ht := countedTransferProgram_trace (10 : Fin 23) src 4 (0 : Fin 8) 1
    h10 (by decide) h4 (by decide) segment rest (a.stacks 10) a.regs a.stacks hs rfl hlen
  have hh := halt_after_trace _ ht 4 rfl rfl
  exact .call _ (by simpa [taken, countedTransferResult, StructuredProgram.State.withPC,
    countedTransferProgram, Nat.add_assoc] using hh)

theorem restore_eval (a : Data) (dst : Fin 23) (h4 : (4 : Fin 23) ≠ dst) :
    Eval (restore dst) (3 * (a.stacks 4).length + 3) a (restored a dst) := by
  have ht := transferProgram_trace (4 : Fin 23) dst (0 : Fin 8) 1 h4 (by decide)
    a.regs a.stacks
  have hh := halt_after_trace _ ht 3 rfl rfl
  exact .call _ (by simpa [restore, restored, transferResult, StructuredProgram.State.withPC,
    transferProgram, Nat.add_assoc] using hh)

theorem pull_eval (a : Data) (src dst : Fin 23) (segment rest : List Bool)
    (hsrc : src ≠ 4 ∧ src ≠ 10 ∧ src ≠ 21)
    (hdst : dst ≠ 4 ∧ dst ≠ 10 ∧ dst ≠ 21) (hsd : src ≠ dst)
    (h0 : a.stacks 0 = []) (h4 : a.stacks 4 = []) (h10 : a.stacks 10 = [])
    (hd : a.stacks dst = []) (hs : a.stacks src = segment ++ rest)
    (hlen : (a.stacks 21).length = segment.length) :
    Eval (pull src dst) (14 * segment.length + 11) a
      (pulled a src dst segment rest) := by
  have hc := copyWidth_eval a h0
  have ht := take_eval (copiedWidth a) src segment rest hsrc.2.1.symm hsrc.1
    (by simpa [copiedWidth, copyStacks, hsrc.2.1, hsrc.2.2] using hs)
    (by simpa [copiedWidth, copyStacks, h10] using hlen)
  have hr := restore_eval (taken (copiedWidth a) src segment rest) dst hdst.1.symm
  have hfinish : restored (taken (copiedWidth a) src segment rest) dst =
      pulled a src dst segment rest := by
    apply MatrixProgramSupport.data_ext
    · simp [ readRegs_reset]
    · funext j
      by_cases hjd : j = dst
      · subst j
        simp [ transferStacks,
          countedTransferStacks, copyStacks,
          hdst.1, hdst.2.1, hsd.symm, hd, h4]
      · by_cases hjs : j = src
        · subst j
          simp [ transferStacks,
            countedTransferStacks, copyStacks, hjd, hsrc.1 ]
        · by_cases hj4 : j = 4
          · subst j
            simp [ transferStacks,
              countedTransferStacks, copyStacks, hjd, hjs, h4]
          · by_cases hj10 : j = 10
            · subst j
              simp [ transferStacks,
                countedTransferStacks, copyStacks, hjd, hjs, h10]
            · simp [ transferStacks,
                countedTransferStacks, copyStacks, hjd, hjs, hj4, hj10]
  rw [hfinish] at hr
  have he := hc.seq (ht.seq hr)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  simp [ countedTransferStacks, copyStacks, h4, hlen]
  ring

theorem pullFour_eval (a : Data) (words rests : Fin 4 → List Bool)
    (h0 : a.stacks 0 = []) (h4 : a.stacks 4 = []) (h10 : a.stacks 10 = [])
    (hd : ∀ i, a.stacks (target i) = [])
    (hs : ∀ i, a.stacks (source i) = words i ++ rests i)
    (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
    Eval pullFour (56 * (a.stacks 21).length + 44) a (fourPulled a words rests) := by
  let a1 := pulled a 17 13 (words 0) (rests 0)
  let a2 := pulled a1 18 14 (words 1) (rests 1)
  let a3 := pulled a2 19 15 (words 2) (rests 2)
  have t0 := pull_eval a 17 13 (words 0) (rests 0)
    (by decide) (by decide) (by decide) h0 h4 h10 (hd 0) (hs 0) (hlen 0).symm
  have t1 := pull_eval a1 18 14 (words 1) (rests 1)
    (by decide) (by decide) (by decide)
    (by simp [a1, h0]) (by simp [a1, h4]) (by simp [a1, h10])
    (by simpa [a1, pulled, target] using hd 1)
    (by simpa [a1, pulled, source] using hs 1)
    (by simpa [a1, pulled] using (hlen 1).symm)
  have t2 := pull_eval a2 19 15 (words 2) (rests 2)
    (by decide) (by decide) (by decide)
    (by simp [a2, a1, h0]) (by simp [a2, a1, h4])
    (by simp [a2, a1, h10])
    (by simpa [a2, a1, pulled, target] using hd 2)
    (by simpa [a2, a1, pulled, source] using hs 2)
    (by simpa [a2, a1, pulled] using (hlen 2).symm)
  have t3 := pull_eval a3 20 16 (words 3) (rests 3)
    (by decide) (by decide) (by decide)
    (by simp [a3, a2, a1, h0]) (by simp [a3, a2, a1, h4])
    (by simp [a3, a2, a1, h10])
    (by simpa [a3, a2, a1, pulled, target] using hd 3)
    (by simpa [a3, a2, a1, pulled, source] using hs 3)
    (by simpa [a3, a2, a1, pulled] using (hlen 3).symm)
  have hfinish : pulled a3 20 16 (words 3) (rests 3) = fourPulled a words rests := by
    apply MatrixProgramSupport.data_ext
    · simp [ a3, a2, a1, readRegs_reset]
    · funext j
      fin_cases j <;> simp [ a3, a2, a1]
  rw [hfinish] at t3
  have he := t0.seq (t1.seq (t2.seq t3))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rw [hlen 0, hlen 1, hlen 2, hlen 3]
  ring

end SubexponentialSAT.Subexp.MatrixColorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

open BitProgram StructuredCalls StackRoutines

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 8 => k.val) h

theorem smallStacks_injective : Function.Injective smallStacks := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 17 => k.val) h

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (compared a (decide (a.stacks 1 = a.stacks 12))) := by
  let x : State 5 13 := ⟨fun j => a.regs (smallRegs j), fun j => a.stacks (smallStacks j)⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  have hstart : embedState smallRegs smallStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective smallStacks_injective
    · intro i; rfl
    · intros; rfl
    · intro i; rfl
    · intros; rfl
  have hfinish : embedState smallRegs smallStacks a
      (CollisionStreamProgram.sealed x (decide (x.stacks 1 = x.stacks 12))) =
      compared a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective smallStacks_injective
    · intro i; fin_cases i <;> norm_num [compared, CollisionStreamProgram.sealed, smallRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h
        exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro i; fin_cases i <;> simp [ CollisionStreamProgram.sealed, x, smallStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityInner smallRegs smallStacks a
    smallRegs_injective smallStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · change n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 at hn
    omega
  · simpa only [hstart, hfinish, equality] using he

theorem copy_eval (a : Data) (src dst : Fin 17) (hsd : src ≠ dst)
    (hs0 : src ≠ 0) (h0d : (0 : Fin 17) ≠ dst) (h0 : a.stacks 0 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 0 (0 : Fin 8) 1 hsd hs0 h0d (by decide) a h0

theorem prepare_eval (a : Data) (swapped : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = []) :
    Eval (prepare swapped) (7 * volume a + 20) a (prepared a swapped) := by
  let a1 := copied a (firstSource swapped) 1
  let a2 := copied a1 (secondSource swapped) 1
  let a3 := copied a2 16 12
  let a4 := copied a3 15 12
  have t0 := copy_eval a (firstSource swapped) 1
    (by cases swapped <;> decide) (by cases swapped <;> decide) (by decide) h0
  have t1 := copy_eval a1 (secondSource swapped) 1
    (by cases swapped <;> decide) (by cases swapped <;> decide) (by decide)
    (by cases swapped <;> simp [a1, copyStacks, h0, firstSource])
  have t2 := copy_eval a2 16 12 (by decide) (by decide) (by decide)
    (by cases swapped <;> simp [a2, a1, copyStacks, h0, firstSource, secondSource])
  have t3 := copy_eval a3 15 12 (by decide) (by decide) (by decide)
    (by cases swapped <;> simp [a3, a2, a1, copyStacks, h0, firstSource, secondSource])
  have he : copied a3 15 12 = prepared a swapped := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; cases swapped <;> fin_cases j <;>
        simp [a3, a2, a1, readRegs]
    · funext j; cases swapped <;> fin_cases j <;>
        simp [a3, a2, a1, copyStacks, leftWord,
          firstSource, secondSource, h1, h12]
  have ht := t0.seq (t1.seq (t2.seq t3))
  rw [he] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  cases swapped <;> simp [a3, a2, a1, copyStacks, firstSource, secondSource, volume] <;> ring

theorem comparePair_eval (a : Data) (swapped : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 18 * volume a + 40,
      Eval (comparePair swapped) n a (compared a (pairMatches a swapped)) := by
  have hp := prepare_eval a swapped h0 h1 h12
  obtain ⟨n, hn, he⟩ := equality_eval (prepared a swapped)
  have hfinish : compared (prepared a swapped)
      (decide ((prepared a swapped).stacks 1 = (prepared a swapped).stacks 12)) =
      compared a (pairMatches a swapped) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [ readRegs]
    · funext j; fin_cases j <;> simp [ pairMatches]
  rw [hfinish] at he
  refine ⟨7 * volume a + 20 + n, ?_, hp.seq he⟩
  cases swapped <;> simp [ leftWord, List.length_append, volume] at hn ⊢ <;> omega

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical active-position step for a normalized matrix entry.
Stack 2 counts unchanged nonfixed pairs, stack 3 counts swapped nonfixed
pairs, and register 7 records compatibility of all positions seen so far. -/

namespace SubexponentialSAT.Subexp.MatrixPositionCountProgram

open BitProgram StructuredCalls StackRoutines MatrixPositionProgram

theorem popResult_eval (a : Data) (out : Fin 8) : Eval (popResult out) 1 a (popped a out) :=
  .base (.atom _ _)

theorem branch_eval (a : Data) : ∃ n ≤ 4, Eval branch n a (branched a) := by
  cases h6 : a.regs 6 <;> cases h4 : a.regs 4
  · refine ⟨3, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_false h6 (Eval.ite_false h4 (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.set (7 : Fin 8) false) a)))
  · refine ⟨4, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_false h6 (Eval.ite_true h4 (TupleProgram.pushConst_eval (3 : Fin 17) (0 : Fin 8) true a))
  · refine ⟨4, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, Bool.false_eq_true, ↓reduceIte] using
      Eval.ite_true h6 (Eval.ite_false h4 (TupleProgram.pushConst_eval (2 : Fin 17) (0 : Fin 8) true a))
  · refine ⟨2, by decide, ?_⟩
    simpa only [branch, branched, h6, h4, ↓reduceIte] using
      Eval.ite_true h6 (Eval.ite_true h4 (Eval.base (StructuredProgram.Eval.skip a)))

theorem reset_eval (a : Data) : Eval reset 4 a (resetState a) := by
  let a1 := (StructuredProgram.Atom.set (0 : Fin 8) false).eval a
  let a2 := (StructuredProgram.Atom.set (4 : Fin 8) false).eval a1
  let a3 := (StructuredProgram.Atom.set (5 : Fin 8) false).eval a2
  have h := (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false) a)).seq
    ((Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (4 : Fin 8) false) a1)).seq
      ((Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (5 : Fin 8) false) a2)).seq
        (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) false) a3))))
  simpa [reset, resetState, a3, a2, a1, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

private theorem pairMatches_popped_compared (a : Data) (answer : Bool)
    (out : Fin 8) (swapped : Bool) :
    pairMatches (popped (compared a answer) out) swapped = pairMatches a swapped := by
  cases swapped <;> simp [pairMatches, leftWord, popped ]

private theorem volume_popped_compared (a : Data) (answer : Bool) (out : Fin 8) :
    volume (popped (compared a answer) out) = volume a := by
  simp [volume, popped ]

theorem command_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 36 * volume a + 90, Eval command n a (classified a) := by
  let a1 := compared a (pairMatches a false)
  let a2 := popped a1 6
  let a3 := compared a2 (pairMatches a true)
  let a4 := popped a3 4
  let a5 := branched a4
  obtain ⟨n1, hn1, t1⟩ := comparePair_eval a false h0 h1 h12
  have t2 := popResult_eval a1 6
  obtain ⟨n3, hn3, t3⟩ := comparePair_eval a2 true
    (by simp [a2, a1, popped, h0])
    (by simp [a2, a1, popped ])
    (by simp [a2, a1, popped ])
  have hmatch : pairMatches a2 true = pairMatches a true :=
    pairMatches_popped_compared a (pairMatches a false) 6 true
  rw [hmatch] at t3
  have t4 := popResult_eval a3 4
  obtain ⟨n5, hn5, t5⟩ := branch_eval a4
  have t6 := reset_eval a5
  have hfinish : resetState a5 = classified a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      cases hs : pairMatches a false <;> cases hw : pairMatches a true <;> fin_cases j <;>
        simp [a5, a4, a3, a2, a1, branched, popped, hs, hw, readRegs, h11,
          TupleProgram.pushedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    · funext j
      cases hs : pairMatches a false <;> cases hw : pairMatches a true <;> fin_cases j <;>
        simp [a5, a4, a3, a2, a1, branched, popped, hs, hw, readRegs, h1, h11, h12,
          TupleProgram.pushedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  rw [hfinish] at t6
  refine ⟨n1 + (1 + (n3 + (1 + (n5 + 4)))), ?_,
    t1.seq (t2.seq (t3.seq (t4.seq (t5.seq t6))))⟩
  have hv : volume a2 = volume a := volume_popped_compared a (pairMatches a false) 6
  rw [hv] at hn3
  omega

theorem program_runsIn (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    RunsIn program (36 * volume a + 91)
      (a.withPC (some program.entry)) ((classified a).withPC none) := by
  obtain ⟨n, hn, ht⟩ := command_eval a h0 h1 h11 h12
  exact ⟨n + 1, by omega, compiled_halt_trace ht 13 2⟩

end SubexponentialSAT.Subexp.MatrixPositionCountProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

theorem lowPorts_injective : Function.Injective lowPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 23 => k.val) h

theorem embed_eq_frame (base : Data) (a : MatrixPositionProgram.Data) :
    embedState id lowPorts base a = frame base a := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; simp [frame, lowPorts, i.isLt]
  · intro i hi
    have h : ¬ i.val < 17 := by
      intro h
      exact hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    simp [frame, h]

theorem frame_restrict (a : Data) : frame a (restrict a) = a := by
  apply MatrixProgramSupport.data_ext
  · rfl
  · funext j
    by_cases h : j.val < 17
    · simp [frame, restrict, lowPorts]
    · simp [frame, h]

theorem classify_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 36 * MatrixPositionProgram.volume (restrict a) + 91,
      Eval classify n a (classified a) := by
  obtain ⟨n, hn, ht⟩ := MatrixPositionCountProgram.program_runsIn (restrict a) h0 h1 h11 h12
  have he := eval_call_lifted MatrixPositionCountProgram.program id lowPorts a
    Function.injective_id lowPorts_injective ht
  rw [embed_eq_frame, embed_eq_frame, frame_restrict] at he
  exact ⟨n, hn, he⟩

theorem clear_eval (a : Data) (i : Fin 23) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a (clearedOne a i) :=
  TupleProgram.clear_eval i (0 : Fin 8) 1 a

theorem clearWords_eval (a : Data) :
    Eval clearWords (2 * MatrixPositionProgram.volume (restrict a) + 12) a (cleared a) := by
  have h0 := clear_eval a 13
  have h1 := clear_eval (clearedOne a 13) 14
  have h2 := clear_eval (clearedOne (clearedOne a 13) 14) 15
  have h3 := clear_eval (clearedOne (clearedOne (clearedOne a 13) 14) 15) 16
  have he := h0.seq (h1.seq (h2.seq h3))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [cleared, clearedOne, clearStacks,
    MatrixPositionProgram.volume, restrict, lowPorts] <;> ring

theorem command_eval_oai (a : Data) (words rests : Fin 4 → List Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h4 : a.stacks 4 = [])
    (h10 : a.stacks 10 = []) (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = [])
    (hd : ∀ i, a.stacks (MatrixColorReadProgram.target i) = [])
    (hs : ∀ i, a.stacks (MatrixColorReadProgram.source i) = words i ++ rests i)
    (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
    ∃ n ≤ 208 * (a.stacks 21).length + 147,
      Eval command n a (output a words rests) := by
  have hp := MatrixColorReadProgram.pullFour_eval a words rests h0 h4 h10 hd hs hlen
  let b := MatrixColorReadProgram.fourPulled a words rests
  obtain ⟨nc, hnc, hc⟩ := classify_eval b
    (by simp [b, h0])
    (by simp [b, h1])
    (by simp [b, h11])
    (by simp [b, h12])
  have hclear := clearWords_eval (classified b)
  have hvol : MatrixPositionProgram.volume (restrict b) = 4 * (a.stacks 21).length := by
    change (b.stacks 13).length + (b.stacks 14).length +
      (b.stacks 15).length + (b.stacks 16).length = _
    have h13 : b.stacks 13 = words 0 := rfl
    have h14 : b.stacks 14 = words 1 := rfl
    have h15 : b.stacks 15 = words 2 := rfl
    have h16 : b.stacks 16 = words 3 := rfl
    rw [h13, h14, h15, h16, hlen 0, hlen 1, hlen 2, hlen 3]
    omega
  have hvol' : MatrixPositionProgram.volume (restrict (classified b)) =
      MatrixPositionProgram.volume (restrict b) := by
    change ((classified b).stacks 13).length + ((classified b).stacks 14).length +
      ((classified b).stacks 15).length + ((classified b).stacks 16).length =
      (b.stacks 13).length + (b.stacks 14).length + (b.stacks 15).length + (b.stacks 16).length
    have hc13 : (classified b).stacks 13 = b.stacks 13 := rfl
    have hc14 : (classified b).stacks 14 = b.stacks 14 := rfl
    have hc15 : (classified b).stacks 15 = b.stacks 15 := rfl
    have hc16 : (classified b).stacks 16 = b.stacks 16 := rfl
    rw [hc13, hc14, hc15, hc16]
  refine ⟨56 * (a.stacks 21).length + 44 +
    (nc + (2 * MatrixPositionProgram.volume (restrict (classified b)) + 12)), ?_,
    hp.seq (hc.seq hclear)⟩
  rw [hvol] at hnc
  rw [hvol', hvol]
  omega

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval_oai
