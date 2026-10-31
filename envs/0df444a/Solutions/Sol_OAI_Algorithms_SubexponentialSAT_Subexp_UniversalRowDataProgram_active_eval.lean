-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:36:52.50912+00:00
-- url     : https://prove2.me/submissions/e717f969-a925-4be5-a4a6-1c16e59588b7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowFactorLoop_loop_indices_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGather
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

open BitProgram StructuredCalls StackRoutines

theorem readPorts_injective (field : Field) : Function.Injective (readPorts field) := by
  cases field <;> decide

/-- Each read has a fixed port map. Table widths and the selected position
are consumed only as runtime words by the existing array-access program. -/
theorem readIndex_eval (field : Field) (rows : List Word) (width index : Word) (a : Data)
    (harray : a.stacks (arrayPort field) = rows.flatten)
    (hwidth : a.stacks (widthPort field) = width) (hindex : a.stacks 16 = index)
    (hi : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (outputPort field) = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval (readIndex field) (index.length * (14 * width.length + 17) + 15 * width.length + 21)
      a (result field a (rows.getD index.length [])) := by
  let copied := SubexpScanPrimitives.afterCopy a 16 2 0 1
  have hc := SubexpScanPrimitives.copy_eval a 16 2 15 0 1
    (by decide) (by decide) (by decide) (by decide) h15
  let inner : State 8 8 := ⟨copied.regs, copied.stacks ∘ readPorts field⟩
  have htake : (rows.take index.length).length = index.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hrow : (rows.getD index.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hrows _ (List.getElem_mem hi)
  have hs : inner.stacks 0 = (rows.take index.length).flatten ++
      (rows.getD index.length [] ++ (rows.drop (index.length + 1)).flatten) := by
    have ha : inner.stacks 0 = rows.flatten := by
      cases field <;> simpa [inner, copied, SubexpScanPrimitives.afterCopy,
        copyStacks, readPorts, arrayPort] using harray
    exact ha.trans (GatherProgram.row_decomposition rows _ hi)
  have hw : inner.stacks 3 = width := by
    cases field <;> simpa [inner, copied, SubexpScanPrimitives.afterCopy,
      copyStacks, readPorts, widthPort] using hwidth
  have hidx : inner.stacks 2 = index := by
    simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, hindex, h2]
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    (rows.take index.length) (rows.getD index.length [])
    (rows.drop (index.length + 1)).flatten width index inner.regs inner.stacks
    hs hw hidx htake.symm (fun row hr => hrows row (List.mem_of_mem_take hr)) hrow
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h4])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h5])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h6])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h7])
  have hin : embedState id (readPorts field) copied inner = copied := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (readPorts_injective field)
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hend : embedState id (readPorts field) copied
      ⟨readRegs inner.regs 0 1 none,
        ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩ =
      result field a (rows.getD index.length []) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (readPorts_injective field)
    · intro j; simp [result, inner, copied, SubexpScanPrimitives.afterCopy, readRegs_reset]
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j
      cases field <;> fin_cases j <;>
        simp_all [result, inner, copied, SubexpScanPrimitives.afterCopy, copyStacks,
          readPorts, arrayPort, outputPort, widthPort, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have ho : j ≠ outputPort field := fun h => hj ⟨1, h.symm⟩
      have hidx : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [result, copied, SubexpScanPrimitives.afterCopy, copyStacks, ho, hidx]
  have hr := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (readPorts field) copied Function.injective_id (readPorts_injective field)
    (a := inner) (b := ⟨readRegs inner.regs 0 1 none,
      ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩) ht
  rw [hin, hend] at hr
  have run := hc.seq hr
  convert run using 1
  all_goals try with_reducible_and_instances rfl
  simp [ hindex, htake]
  ring

theorem termFields_eval (values inverses differences : List Word)
    (width rowWidth index : Word) (a : Data)
    (hv : a.stacks 24 = values.flatten) (hinv : a.stacks 25 = inverses.flatten)
    (hdiff : a.stacks 27 = differences.flatten)
    (hw : a.stacks 29 = width) (hrw : a.stacks 30 = rowWidth) (hi : a.stacks 16 = index)
    (hvi : index.length < values.length) (hii : index.length < inverses.length)
    (hdi : index.length < differences.length)
    (hvs : ∀ row ∈ values, row.length = width.length)
    (his : ∀ row ∈ inverses, row.length = width.length)
    (hds : ∀ row ∈ differences, row.length = rowWidth.length)
    (h0 : a.stacks 0 = []) (h19 : a.stacks 19 = []) (h20 : a.stacks 20 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval termFields
      (index.length * (28 * width.length + 14 * rowWidth.length + 51) +
        30 * width.length + 15 * rowWidth.length + 63)
      a (termResult a (values.getD index.length []) (inverses.getD index.length [])
        (differences.getD index.length [])) := by
  let a1 := result .value a (values.getD index.length [])
  let a2 := result .inverse a1 (inverses.getD index.length [])
  have h1 := readIndex_eval .value values width index a hv hw hi hvi hvs h19
    h2 h4 h5 h6 h7 h15
  have h2' := readIndex_eval .inverse inverses width index a1
    (by simpa [a1, result, outputPort, arrayPort] using hinv)
    (by simpa [a1, result, outputPort, widthPort] using hw)
    (by simpa [a1, result, outputPort] using hi) hii his
    (by simpa [a1, result, outputPort] using h20)
    (by simpa [a1, result, outputPort] using h2)
    (by simpa [a1, result, outputPort] using h4)
    (by simpa [a1, result, outputPort] using h5)
    (by simpa [a1, result, outputPort] using h6)
    (by simpa [a1, result, outputPort] using h7)
    (by simpa [a1, result, outputPort] using h15)
  have h3 := readIndex_eval .difference differences rowWidth index a2
    (by simpa [a2, a1, result, outputPort, arrayPort] using hdiff)
    (by simpa [a2, a1, result, outputPort, widthPort] using hrw)
    (by simpa [a2, a1, result, outputPort] using hi) hdi hds
    (by simpa [a2, a1, result, outputPort] using h0)
    (by simpa [a2, a1, result, outputPort] using h2)
    (by simpa [a2, a1, result, outputPort] using h4)
    (by simpa [a2, a1, result, outputPort] using h5)
    (by simpa [a2, a1, result, outputPort] using h6)
    (by simpa [a2, a1, result, outputPort] using h7)
    (by simpa [a2, a1, result, outputPort] using h15)
  have ht := h1.seq (h2'.seq h3)
  convert ht using 1
  · ring
  · simp [termResult, a2, a1, result, outputPort, readRegs_reset]

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)

theorem resetFlags_eval (a : Data) : Eval resetFlags 3 a (resetState a) := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (5 : Fin 8) false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) true)
    ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a))
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (7 : Fin 8) false)
    ((StructuredProgram.Atom.set (6 : Fin 8) true).eval
      ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a)))
  exact h1.seq (h2.seq h3)

theorem unread_false (records : List Word) (suffix : Word) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa [RecordPrograms.unread] using ih

theorem any_false {α : Type*} (xs : List α) : xs.any (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermFraming
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical framing of a gathered correction term and the final row. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermFraming

open BitProgram StructuredCalls

theorem term_eval (a : Data) (value inverse : Word)
    (fs : List (UniversalRowProgram.Factor Word))
    (hv : a.stacks 19 = value) (hi : a.stacks 20 = inverse)
    (hf : a.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor fs)
    (h23 : a.stacks 23 = []) :
    ∃ b : Data,
      Eval term (termCost value inverse (Encoding.encodeList UniversalRowProgram.encodeFactor fs)) a b ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 19 []) 20 []) 21 []) 31
        (true :: (Encoding.frame (UniversalRowProgram.encodeTerm ⟨value, inverse, fs⟩) ++
          a.stacks 31)) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 20 21 23
    (by decide) (by decide) (by decide) a h23
  obtain ⟨c, hc, hcs⟩ := MatrixProgramSupport.emitFrame_eval 19 21 23
    (by decide) (by decide) (by decide) b (by rw [hbs]; simpa using h23)
  obtain ⟨d, hd, hds⟩ := MatrixProgramSupport.emitFrame_eval 21 31 23
    (by decide) (by decide) (by decide) c (by rw [hcs, hbs]; simpa using h23)
  let e := TupleProgram.pushedState (31 : Fin 32) (0 : Fin 8) true d
  have he := TupleProgram.pushConst_eval (31 : Fin 32) (0 : Fin 8) true d
  refine ⟨e, ?_, ?_⟩
  · have ht := hb.seq (hc.seq (hd.seq he))
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    simp [termCost, hcs, hbs, hv, hi, hf, Encoding.length_frame]
    ring
  · simp only [e ]
    rw [hds, hcs, hbs]
    funext j
    by_cases h19 : j = 19 <;> by_cases h20 : j = 20 <;>
      by_cases h21 : j = 21 <;> by_cases h31 : j = 31 <;>
        simp_all [ UniversalRowProgram.encodeTerm, List.append_assoc]

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

theorem command_eval (values inverses negatives rows differences : List Word)
    (width rowWidth : Word) (positions : List ℕ) (i : ℕ) (a : Data)
    (ha : Ready values inverses negatives rows width rowWidth positions i a)
    (hvi : i < values.length) (hii : i < inverses.length) (hri : i < rows.length)
    (hvs : ∀ row ∈ values, row.length = width.length)
    (his : ∀ row ∈ inverses, row.length = width.length)
    (hrs : ∀ row ∈ rows, row.length = rowWidth.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hrow : rows.getD i [] = differences.flatten)
    (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length) :
    ∃ n ≤ cost values inverses negatives differences width rowWidth positions i,
      ∃ b : Data, Eval command n a b ∧
        b.regs 5 = false ∧ b.regs 6 = true ∧ b.regs 7 = false ∧
        b.stacks = Function.update (Function.update a.stacks 16 []) 31
          (true :: (Encoding.frame
            (UniversalRowProgram.encodeTerm (term values inverses negatives differences positions i)) ++
              a.stacks 31)) := by
  let a1 := UniversalRowGather.termResult a (values.getD i []) (inverses.getD i []) (rows.getD i [])
  have hfields := UniversalRowGather.termFields_eval values inverses rows width rowWidth (indexWord i) a
    ha.values ha.inverses ha.rows ha.width ha.rowWidth ha.index
    (by simpa using hvi) (by simpa using hii) (by simpa using hri) hvs his hrs
    (ha.empty 0 (by simp)) (ha.empty 19 (by simp)) (ha.empty 20 (by simp))
    (ha.empty 2 (by simp)) (ha.empty 4 (by simp)) (ha.empty 5 (by simp))
    (ha.empty 6 (by simp)) (ha.empty 7 (by simp)) (ha.empty 15 (by simp))
  simp only [UniversalRowFactorLoop.indexWord_length] at hfields
  let a2 : Data := ⟨readRegs a1.regs 0 1 none, copyStacks 28 8 a1.stacks⟩
  have hcopy := TupleProgram.copy_eval 28 8 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simpa [a1, UniversalRowGather.termResult] using ha.empty 15 (by simp))
  let a3 := TupleProgram.pushedState (21 : Fin 32) (0 : Fin 8) false a2
  have hinit := TupleProgram.pushConst_eval (21 : Fin 32) (0 : Fin 8) false a2
  have hready : UniversalRowFactorLoop.Ready differences negatives width (indexWord i) a3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrow
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.negatives
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.width
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.index
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
          using ha.empty _ (by simp)
  have hacc : a3.stacks 21 = [false] := by
    simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
      using congrArg (List.cons false) (ha.empty 21 (by simp))
  obtain ⟨nl, hnl, next, hloop, hnext, hfactor, hframe⟩ :=
    UniversalRowFactorLoop.loop_indices_eval differences negatives width i positions [] a3
      hready hacc hds hns hpositions (a3.regs 5) (a3.regs 6) (a3.regs 7)
  have hstart : RecordPrograms.state UniversalRowFactorLoop.ports a3
      (a3.regs 5) (a3.regs 6) (a3.regs 7)
      (Encoding.encodeList id (positions.reverse.map indexWord) ++ []) [] = a3 := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simp [a3, a2, a1, UniversalRowGather.termResult, copyStacks,
        UniversalRowFactorLoop.ports, ha.indices, ha.empty 8 (by simp), indices]
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks,
        UniversalRowFactorLoop.ports] using ha.empty 9 (by simp)
  rw [hstart] at hloop
  let a4 := RecordPrograms.state UniversalRowFactorLoop.ports next false true false [] []
  have h4 : a4.stacks = Function.update (Function.update a1.stacks 8 []) 21
      (Encoding.encodeList UniversalRowProgram.encodeFactor
        (UniversalRowFactorLoop.factors differences negatives i positions)) := by
    funext j
    by_cases hj8 : j = 8
    · subst j
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports]
    by_cases hj9 : j = 9
    · subst j
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports, a1,
        UniversalRowGather.termResult, ha.empty 9 (by simp)]
    by_cases hj21 : j = 21
    · subst j
      simpa [a4, RecordPrograms.state, UniversalRowFactorLoop.ports] using hfactor
    · have hf := hframe j hj21
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports, hj8, hj9, hj21,
        hf, a3, a2, copyStacks]
  obtain ⟨a5, hterm, h5⟩ := UniversalRowTermFraming.term_eval a4
    (values.getD i []) (inverses.getD i [])
    (UniversalRowFactorLoop.factors differences negatives i positions)
    (by simp [h4, a1, UniversalRowGather.termResult])
    (by simp [h4, a1, UniversalRowGather.termResult])
    (by simp [h4])
    (by simpa [h4, a1, UniversalRowGather.termResult] using ha.empty 23 (by simp))
  let a6 : Data := ⟨readRegs a5.regs 0 1 none, clearStacks 0 a5.stacks⟩
  let a7 : Data := ⟨readRegs a6.regs 0 1 none, clearStacks 16 a6.stacks⟩
  have hclear0 := TupleProgram.clear_eval 0 (0 : Fin 8) 1 a5
  have hclear16 := TupleProgram.clear_eval 16 (0 : Fin 8) 1 a6
  have hreset := UniversalRowFactorLoop.resetFlags_eval a7
  have hrun := hfields.seq (hcopy.seq (hinit.seq (hloop.seq
    (hterm.seq (hclear0.seq (hclear16.seq hreset))))))
  let b := UniversalRowFactorLoop.resetState a7
  have hrowsize : (rows.getD i []).length = rowWidth.length := by
    rw [List.getD_eq_getElem _ _ hri]
    exact hrs _ (List.getElem_mem hri)
  refine ⟨_, ?_, b, hrun, ?_, ?_, ?_, ?_⟩
  · have hc : a1.stacks 28 = indices positions := by
      simpa [a1, UniversalRowGather.termResult] using ha.indices
    have hzero : a5.stacks 0 = rows.getD i [] := by
      simp [h5, h4, a1, UniversalRowGather.termResult]
    have hi : a6.stacks 16 = indexWord i := by
      simpa [a6, clearStacks, h5, h4, a1, UniversalRowGather.termResult] using ha.index
    simp only [hc, hzero, hi, hrowsize, UniversalRowFactorLoop.indexWord_length]
    unfold cost
    omega
  · simp [b ]
  · simp [b ]
  · simp [b ]
  · funext j
    have he0 := ha.empty 0 (by simp)
    have he8 := ha.empty 8 (by simp)
    have he19 := ha.empty 19 (by simp)
    have he20 := ha.empty 20 (by simp)
    have he21 := ha.empty 21 (by simp)
    by_cases hj0 : j = 0
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he0]
    by_cases hj8 : j = 8
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he8]
    by_cases hj16 : j = 16
    · subst j; simp [b, a7, a6, clearStacks]
    by_cases hj19 : j = 19
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he19]
    by_cases hj20 : j = 20
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he20]
    by_cases hj21 : j = 21
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he21]
    by_cases hj31 : j = 31
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, term]
    · simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, hj0, hj8, hj16, hj19, hj20, hj21, hj31]

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

theorem rows_getD (t : Tables) (i : ℕ) :
    t.rows.getD i [] = (t.differences.getD i []).flatten := by
  rcases t with ⟨values, inverses, negatives, differences⟩
  induction differences generalizing i with
  | nil => simp [Tables.rows]
  | cons d ds ih =>
      cases i <;> simp_all [Tables.rows]

theorem callback_contract (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (frame : Fin 32 → Word) :
    RecordPrograms.CallbackContractWithOn ports UniversalRowTermProgram.command (fun _ => false)
      (cost t width rowWidth positions) (invariant t width rowWidth positions frame)
      (effect t positions) (fun bits => ∃ i ∈ positions, bits = indexWord i) := by
  intro bits tail base hvalid hbase
  obtain ⟨i, hi, rfl⟩ := hvalid
  let a := RecordPrograms.state ports base false true false tail (indexWord i).reverse
  have ha : UniversalRowTermProgram.Ready t.values t.inverses t.negatives t.rows
      width rowWidth positions i a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [a, RecordPrograms.state, ports] using hbase.1.values
    · simpa [a, RecordPrograms.state, ports] using hbase.1.inverses
    · simpa [a, RecordPrograms.state, ports] using hbase.1.negatives
    · simpa [a, RecordPrograms.state, ports] using hbase.1.rows
    · simpa [a, RecordPrograms.state, ports] using hbase.1.indices
    · simpa [a, RecordPrograms.state, ports] using hbase.1.width
    · simpa [a, RecordPrograms.state, ports] using hbase.1.rowWidth
    · simp [a, RecordPrograms.state, ports]
    · intro j hj
      have he := hbase.1.empty j hj
      fin_cases j <;> simp_all [a, RecordPrograms.state, ports]
  obtain ⟨n, hn, b, hb, h5, h6, h7, hbs⟩ := UniversalRowTermProgram.command_eval
    t.values t.inverses t.negatives t.rows (t.differences.getD i []) width rowWidth positions i a ha
    (valid.bounds i hi).1 (valid.bounds i hi).2.1
    (by simpa [Tables.rows] using (valid.bounds i hi).2.2)
    valid.values valid.inverses valid.rows (valid.differences i hi) valid.negatives
    (rows_getD t i) (valid.innerBounds i hi)
  let next : Data := ⟨b.regs, Function.update base.stacks 31 (b.stacks 31)⟩
  have hnext : invariant t width rowWidth positions frame next := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [next] using hbase.1.values
    · simpa [next] using hbase.1.inverses
    · simpa [next] using hbase.1.negatives
    · simpa [next] using hbase.1.rows
    · simpa [next] using hbase.1.indices
    · simpa [next] using hbase.1.width
    · simpa [next] using hbase.1.rowWidth
    · simpa [next] using hbase.1.index
    · intro j hj
      have he := hbase.1.empty j hj
      fin_cases j <;> simp_all [next]
    · intro j hj
      simpa [next, hj] using hbase.2 j hj
  have hend : b = RecordPrograms.state ports next false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp_all [ next, ports]
    · funext j
      rw [hbs]
      by_cases hj16 : j = 16 <;> by_cases hj17 : j = 17 <;> by_cases hj31 : j = 31 <;>
        simp_all [RecordPrograms.state, next, a, ports, Function.update_apply]
  refine ⟨n, next, ?_, hnext, ?_, ?_⟩
  · simpa [cost] using hn
  · simp [effect, next, hbs, a, RecordPrograms.state, ports, prepend, term]
  · rw [← hend]
    exact hb

theorem output_append (t : Tables) (positions : List ℕ) (xs ys : List Word) (acc : Word) :
    output t positions (xs ++ ys) acc = output t positions ys (output t positions xs acc) := by
  simp [output, List.foldl_append]

theorem output_reverse (t : Tables) (positions traversal : List ℕ)
    (tail : List (UniversalRowProgram.Term Word)) :
    output t positions (traversal.reverse.map indexWord)
        (Encoding.encodeList UniversalRowProgram.encodeTerm tail) =
      Encoding.encodeList UniversalRowProgram.encodeTerm (traversal.map (term t positions) ++ tail) := by
  induction traversal with
  | nil => simp [output]
  | cons i rest ih =>
      rw [List.reverse_cons, List.map_append, output_append]
      change prepend t positions (indexWord i).length
        (output t positions (rest.reverse.map indexWord)
          (Encoding.encodeList UniversalRowProgram.encodeTerm tail)) = _
      rw [ih]
      simp [prepend, Encoding.encodeList]

theorem loop_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (base : Data)
    (hbase : ready t width rowWidth positions base) (hacc : base.stacks 31 = [false])
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (cost t width rowWidth positions) (positions.reverse.map indexWord),
      ∃ next : Data,
        Eval loop n
          (RecordPrograms.state ports base v pr f
            (UniversalRowTermProgram.indices positions) [])
          (RecordPrograms.state ports next false true false [] []) ∧
        ready t width rowWidth positions next ∧
        next.stacks 31 = Encoding.encodeList UniversalRowProgram.encodeTerm
          (positions.map (term t positions)) ∧
        (∀ j, j ≠ 31 → next.stacks j = base.stacks j) := by
  have hv : ∀ bits ∈ positions.reverse.map indexWord, ∃ i ∈ positions, bits = indexWord i := by
    intro bits hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨i, by simpa using hi, rfl⟩
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on ports
    UniversalRowTermProgram.command (fun _ => false) (cost t width rowWidth positions)
    (invariant t width rowWidth positions base.stacks) (effect t positions)
    (fun bits => ∃ i ∈ positions, bits = indexWord i)
    (callback_contract t width rowWidth positions valid base.stacks)
    (positions.reverse.map indexWord) [] base hv ⟨hbase, by intros; rfl⟩ v pr f
  refine ⟨n, hn, next, ?_, hnext.1, ?_, hnext.2⟩
  · simpa [loop, UniversalRowTermProgram.indices, UniversalRowFactorLoop.unread_false,
      UniversalRowFactorLoop.any_false] using he
  · have ho := history.fold_of_false (by intros; rfl) (fun a => a.stacks 31)
      (fun out bits => prepend t positions bits.length out) (by intros; assumption)
    change next.stacks 31 = output t positions (positions.reverse.map indexWord) (base.stacks 31) at ho
    rw [ho, hacc]
    simpa only [Encoding.encodeList, List.append_nil] using output_reverse t positions positions []

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowDataProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

private theorem ready_update (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    {a b : Data} (h : ready t width rowWidth positions a) (port : Fin 32)
    (hp : port = 17 ∨ port = 31) (word : Word)
    (hs : b.stacks = Function.update a.stacks port word) : ready t width rowWidth positions b := by
  rcases hp with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hs] using h.values
    · simpa [hs] using h.inverses
    · simpa [hs] using h.negatives
    · simpa [hs] using h.rows
    · simpa [hs] using h.indices
    · simpa [hs] using h.width
    · simpa [hs] using h.rowWidth
    · simpa [hs] using h.index
    · intro j hj
      have he := h.empty j hj
      fin_cases j <;> simp_all []

theorem active_eval_oai (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (a : Data)
    (ha : ready t width rowWidth positions a) (h17 : a.stacks 17 = [])
    (h31 : a.stacks 31 = [false]) :
    ∃ n ≤ activeCost t width rowWidth positions, ∃ b : Data, Eval active n a b ∧
      b.stacks = Function.update a.stacks 31
        (Encoding.encodeList UniversalRowProgram.encodeTerm
          (positions.map (UniversalRowLoop.term t positions))) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 28 17 a.stacks⟩
  have hc := TupleProgram.copy_eval 28 17 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a (ha.empty 15 (by simp))
  have hready : ready t width rowWidth positions a1 :=
    ready_update t width rowWidth positions ha 17 (Or.inl rfl) (a.stacks 28 ++ a.stacks 17) rfl
  obtain ⟨nl, hnl, next, hl, hn, ho, hf⟩ := UniversalRowLoop.loop_eval t width rowWidth positions
    valid a1 hready (by simpa [a1, copyStacks] using h31) (a1.regs 5) (a1.regs 6) (a1.regs 7)
  have hstart : RecordPrograms.state UniversalRowLoop.ports a1
      (a1.regs 5) (a1.regs 6) (a1.regs 7) (UniversalRowTermProgram.indices positions) [] = a1 := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a1, copyStacks, UniversalRowLoop.ports, h17] using ha.indices
    · simpa [a1, copyStacks, UniversalRowLoop.ports,
        UniversalRowFactorLoop.indexWord] using ha.index
  rw [hstart] at hl
  let b := RecordPrograms.state UniversalRowLoop.ports next false true false [] []
  refine ⟨7 * (a.stacks 28).length + 5 + nl, ?_, b, hc.seq hl, ?_⟩
  · rw [ha.indices]
    unfold activeCost
    omega
  · funext j
    by_cases hj31 : j = 31
    · subst j
      simpa [b, RecordPrograms.state, UniversalRowLoop.ports] using ho
    by_cases hj17 : j = 17
    · subst j
      simp [b, RecordPrograms.state, UniversalRowLoop.ports, h17]
    by_cases hj16 : j = 16
    · subst j
      simpa [b, RecordPrograms.state, UniversalRowLoop.ports,
        UniversalRowFactorLoop.indexWord] using ha.index
    · simp [b, RecordPrograms.state, UniversalRowLoop.ports, hj31, hj17, hj16,
        hf j hj31, a1, copyStacks]

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval_oai
