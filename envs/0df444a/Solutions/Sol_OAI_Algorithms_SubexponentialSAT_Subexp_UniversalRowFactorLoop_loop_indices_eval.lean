-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:02:37.751606+00:00
-- url     : https://prove2.me/submissions/a0932c51-a9f9-4b24-85b7-70f6dbe7baaf

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

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

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed array reads and framing for one interpolation factor. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactors

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)

theorem readAt_eval (ports : Equiv.Perm (Fin 32)) (rows : List Word)
    (width index : Word) (a : Data)
    (ha : a.stacks (ports 24) = rows.flatten)
    (hw : a.stacks (ports 29) = width) (hi : a.stacks (ports 16) = index)
    (hindex : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (ports 19) = []) (h2 : a.stacks (ports 2) = [])
    (h4 : a.stacks (ports 4) = []) (h5 : a.stacks (ports 5) = [])
    (h6 : a.stacks (ports 6) = []) (h7 : a.stacks (ports 7) = [])
    (h15 : a.stacks (ports 15) = []) :
    Eval (readAt ports)
      (index.length * (14 * width.length + 17) + 15 * width.length + 22)
      a ⟨readRegs a.regs 0 1 none, Function.update a.stacks (ports 19) (rows.getD index.length [])⟩ := by
  let inner : Data := ⟨a.regs, a.stacks ∘ ports⟩
  have ht := UniversalRowGather.readIndex_eval .value rows width index inner
    ha hw hi hindex hrows hout h2 h4 h5 h6 h7 h15
  have hin : embedState id ports a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports.injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hend : embedState id ports a
      (UniversalRowGather.result .value inner (rows.getD index.length [])) =
      (⟨readRegs a.regs 0 1 none,
        Function.update a.stacks (ports 19) (rows.getD index.length [])⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports.injective
    · intros; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      simp [UniversalRowGather.result, UniversalRowGather.outputPort, inner,
        Function.update_apply, ports.injective.eq_iff]
    · intro i hi; exact False.elim (hi ⟨ports.symm i, ports.apply_symm_apply i⟩)
  have he := eval_call_lifted (compiled (UniversalRowGather.readIndex .value) 0 0)
    id ports a Function.injective_id ports.injective (compiled_halt_trace ht 0 0)
  simpa only [hin, hend, readAt, Nat.add_assoc] using he

theorem readFactor_eval (differences negatives : List Word) (width index : Word) (a : Data)
    (hd : a.stacks 0 = differences.flatten) (hn : a.stacks 26 = negatives.flatten)
    (hw : a.stacks 29 = width) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval readFactor (2 * index.length * (14 * width.length + 17) + 30 * width.length + 44)
      a ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 1 (differences.getD index.length []))
          12 (negatives.getD index.length [])⟩ := by
  have hp : differencePorts 24 = 0 ∧ differencePorts 19 = 1 ∧ differencePorts 16 = 9 ∧
      differencePorts 29 = 29 ∧ differencePorts 2 = 2 ∧ differencePorts 4 = 4 ∧
      differencePorts 5 = 5 ∧ differencePorts 6 = 6 ∧ differencePorts 7 = 7 ∧
      differencePorts 15 = 15 := by decide
  have hq : negativePorts 24 = 26 ∧ negativePorts 19 = 12 ∧ negativePorts 16 = 9 ∧
      negativePorts 29 = 29 ∧ negativePorts 2 = 2 ∧ negativePorts 4 = 4 ∧
      negativePorts 5 = 5 ∧ negativePorts 6 = 6 ∧ negativePorts 7 = 7 ∧
      negativePorts 15 = 15 := by decide
  let b : Data := ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 1 (differences.getD index.length [])⟩
  have hfirst := readAt_eval differencePorts differences width index a
    (by simpa [hp.1] using hd) (by simpa [hp.2.2.2.1] using hw)
    (by simpa [hp.2.2.1] using hi) hid hds
    (by simpa [hp.2.1] using h1)
    (by simpa [hp.2.2.2.2.1] using h2)
    (by simpa [hp.2.2.2.2.2.1] using h4)
    (by simpa [hp.2.2.2.2.2.2.1] using h5)
    (by simpa [hp.2.2.2.2.2.2.2.1] using h6)
    (by simpa [hp.2.2.2.2.2.2.2.2.1] using h7)
    (by simpa [hp.2.2.2.2.2.2.2.2.2] using h15)
  have hsecond := readAt_eval negativePorts negatives width index b
    (by simpa [b, hq.1] using hn) (by simpa [b, hq.2.2.2.1] using hw)
    (by simpa [b, hq.2.2.1] using hi) hin hns
    (by simpa [b, hq.2.1] using h12)
    (by simpa [b, hq.2.2.2.2.1] using h2)
    (by simpa [b, hq.2.2.2.2.2.1] using h4)
    (by simpa [b, hq.2.2.2.2.2.2.1] using h5)
    (by simpa [b, hq.2.2.2.2.2.2.2.1] using h6)
    (by simpa [b, hq.2.2.2.2.2.2.2.2.1] using h7)
    (by simpa [b, hq.2.2.2.2.2.2.2.2.2] using h15)
  rw [hp.2.1] at hfirst
  rw [hq.2.1] at hsecond
  have ht := hfirst.seq hsecond
  convert ht using 1
  · ring
  · simp [b, StackRoutines.readRegs_reset]

theorem emitFactor_eval (a : Data) (inverse negative : Word)
    (hinv : a.stacks 1 = inverse) (hneg : a.stacks 12 = negative)
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ b : Data, Eval emitFactor (24 * (inverse.length + negative.length) + 42) a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks 1 []) 12 []) 21
        (true :: (Encoding.frame (UniversalRowProgram.encodeFactor ⟨inverse, negative⟩) ++ a.stacks 21)) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 12 22 23
    (by decide) (by decide) (by decide) a h23
  obtain ⟨c, hc, hcs⟩ := MatrixProgramSupport.emitFrame_eval 1 22 23
    (by decide) (by decide) (by decide) b (by rw [hbs]; simpa using h23)
  obtain ⟨d, hd, hds⟩ := MatrixProgramSupport.emitFrame_eval 22 21 23
    (by decide) (by decide) (by decide) c (by rw [hcs, hbs]; simpa using h23)
  let e := TupleProgram.pushedState (21 : Fin 32) (0 : Fin 8) true d
  have he := TupleProgram.pushConst_eval (21 : Fin 32) (0 : Fin 8) true d
  refine ⟨e, ?_, ?_⟩
  · have run := hb.seq (hc.seq (hd.seq he))
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    simp [hbs, hcs, hinv, hneg, h22, Encoding.length_frame]
    ring
  · simp only [e ]
    rw [hds, hcs, hbs]
    funext j
    by_cases h1 : j = 1 <;> by_cases h12 : j = 12 <;>
      by_cases h21 : j = 21 <;> by_cases h22' : j = 22 <;>
      simp_all [Function.update_apply, UniversalRowProgram.encodeFactor ]

end SubexponentialSAT.Subexp.UniversalRowFactors

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)

theorem equalityRegs_injective : Function.Injective equalityRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

theorem equalityStacks_injective : Function.Injective equalityStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (afterEquality a (decide (a.stacks 1 = a.stacks 12))) := by
  let inner : State 5 13 := ⟨a.regs ∘ equalityRegs, a.stacks ∘ equalityStacks⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval inner
  have hin : embedState equalityRegs equalityStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState equalityRegs equalityStacks a
      (CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12))) =
      afterEquality a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intro j
      fin_cases j <;> norm_num [afterEquality, CollisionStreamProgram.sealed, equalityRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h
        exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro j
      fin_cases j <;>
        simp [ CollisionStreamProgram.sealed, inner, equalityStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityProgram equalityRegs equalityStacks a
    equalityRegs_injective equalityStacks_injective
    (a := inner)
    (b := CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12)))
    (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · have hn' : n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 := by
      simpa [inner, equalityStacks] using hn
    omega
  · simpa only [hin, hout, equality] using he

/-- Both unary words are copied before comparison; the original index words
and every surrounding stack survive the diagonal test. -/
theorem compareIndex_eval (a : Data) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h11 : a.stacks 11 = []) (h15 : a.stacks 15 = []) :
    ∃ n ≤ 18 * (a.stacks 9).length + 9 * (a.stacks 16).length + 31,
      Eval compareIndex n a (compared a) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 9 1 a.stacks⟩
  let a2 : Data := ⟨readRegs a1.regs 0 1 none, copyStacks 16 12 a1.stacks⟩
  have hfirst := TupleProgram.copy_eval 9 1 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h15
  have hsecond := TupleProgram.copy_eval 16 12 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simpa [a1, copyStacks] using h15)
  obtain ⟨ne, hne, he⟩ := equality_eval a2
  let a3 := afterEquality a2 (decide (a2.stacks 1 = a2.stacks 12))
  have hp : Eval (RecordPrograms.atom (.pop 11 4 1)) 1 a3 (compared a) := by
    have ht := Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.pop (11 : Fin 32) (4 : Fin 8) 1) a3)
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · have hl : a2.stacks 1 = a.stacks 9 := by simp [a2, a1, copyStacks, h1, h12]
      have hr : a2.stacks 12 = a.stacks 16 := by simp [a2, a1, copyStacks, h1, h12]
      have hz : a2.stacks 11 = [] := by simp [a2, a1, copyStacks, h11]
      have hanswer : a3.stacks 11 = [decide (a.stacks 9 = a.stacks 16)] := by
        change decide (a2.stacks 1 = a2.stacks 12) :: a2.stacks 11 = _
        rw [hl, hr, hz]
      have hregs : a3.regs = (fun j => if j.val < 5 then false else a.regs j) := by
        change (fun j => if j.val < 5 then false else a2.regs j) = _
        funext j
        by_cases hj : j.val < 5
        · simp [hj]
        · have hj0 : j ≠ 0 := by intro heq; subst j; norm_num at hj
          have hj1 : j ≠ 1 := by intro heq; subst j; norm_num at hj
          simp [hj, a2, a1, readRegs, hj0, hj1]
      change (compared a).regs = readRegs a3.regs 4 1 (a3.stacks 11).head?
      rw [hanswer, hregs]
      funext j
      by_cases hj1 : j = 1 <;> by_cases hj4 : j = 4 <;>
        simp_all [ readRegs, Function.update_apply]
    · funext j
      by_cases hj1 : j = 1 <;> by_cases hj12 : j = 12 <;> by_cases hj11 : j = 11 <;>
        simp_all [ a3, a2, a1, afterEquality, copyStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr
          ]
  refine ⟨7 * (a.stacks 9).length + 5 +
    (7 * (a1.stacks 16).length + 5 + (ne + 1)), ?_, ?_⟩
  · simp [a2, a1, copyStacks, h1, h12] at hne ⊢
    omega
  · exact hfirst.seq (hsecond.seq (he.seq hp))

theorem selected_eval (differences negatives : List Word) (width index : Word) (a : Data)
    (hd : a.stacks 0 = differences.flatten) (hn : a.stacks 26 = negatives.flatten)
    (hw : a.stacks 29 = width) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = [])
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ b : Data,
      Eval selected (2 * index.length * (14 * width.length + 17) + 78 * width.length + 86) a b ∧
      b.stacks = Function.update a.stacks 21
        (prependFactor differences negatives index.length (a.stacks 21)) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 1 (differences.getD index.length []))
      12 (negatives.getD index.length [])⟩
  have hr := UniversalRowFactors.readFactor_eval differences negatives width index a
    hd hn hw hi hid hin hds hns h1 h12 h2 h4 h5 h6 h7 h15
  obtain ⟨b, he, hb⟩ := UniversalRowFactors.emitFactor_eval mid
    (differences.getD index.length []) (negatives.getD index.length [])
    (by simp [mid]) (by simp [mid])
    (by simpa [mid] using h22) (by simpa [mid] using h23)
  refine ⟨b, ?_, ?_⟩
  · have hdl : (differences.getD index.length []).length = width.length := by
      rw [List.getD_eq_getElem _ _ hid]
      exact hds _ (List.getElem_mem hid)
    have hnl : (negatives.getD index.length []).length = width.length := by
      rw [List.getD_eq_getElem _ _ hin]
      exact hns _ (List.getElem_mem hin)
    have ht := hr.seq he
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hdl, hnl]
    ring
  · rw [hb]
    funext j
    by_cases hj1 : j = 1 <;> by_cases hj12 : j = 12 <;> by_cases hj21 : j = 21 <;>
      simp_all [mid, prependFactor, factor, Function.update_apply]

theorem resetFlags_eval (a : Data) : Eval resetFlags 3 a (resetState a) := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (5 : Fin 8) false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) true)
    ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a))
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (7 : Fin 8) false)
    ((StructuredProgram.Atom.set (6 : Fin 8) true).eval
      ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a)))
  exact h1.seq (h2.seq h3)

theorem callback_eval (differences negatives : List Word) (width outer index : Word) (a : Data)
    (ha : Ready differences negatives width outer a) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length) :
    ∃ n ≤ callbackCost width.length outer.length index, ∃ b : Data,
      Eval callback n a b ∧ b.regs 5 = false ∧ b.regs 6 = true ∧ b.regs 7 = false ∧
      b.stacks = Function.update (Function.update a.stacks 21
        (updated differences negatives outer index (a.stacks 21))) 9 [] := by
  obtain ⟨nc, hnc, hc⟩ := compareIndex_eval a (ha.empty 1 (by simp))
    (ha.empty 12 (by simp)) (ha.empty 11 (by simp)) (ha.empty 15 (by simp))
  let mid := compared a
  have hbranch : ∃ nb ≤ 2 * index.length * (14 * width.length + 17) + 78 * width.length + 87,
      ∃ b : Data, Eval (.ite 4 (.base .skip) selected) nb mid b ∧
        b.stacks = Function.update a.stacks 21
          (updated differences negatives outer index (a.stacks 21)) := by
    by_cases heq : index = outer
    · refine ⟨1, by omega, mid, ?_, ?_⟩
      · exact .ite_true (by simp [mid, hi, ha.outer, heq]) (.base (.skip _))
      · simp [mid, updated, heq]
    · obtain ⟨b, hb, hbs⟩ := selected_eval differences negatives width index mid
        ha.differences ha.negatives ha.width hi hid hin hds hns
        (ha.empty 1 (by simp)) (ha.empty 12 (by simp))
        (ha.empty 2 (by simp)) (ha.empty 4 (by simp)) (ha.empty 5 (by simp))
        (ha.empty 6 (by simp)) (ha.empty 7 (by simp)) (ha.empty 15 (by simp))
        (ha.empty 22 (by simp)) (ha.empty 23 (by simp))
      refine ⟨2 * index.length * (14 * width.length + 17) + 78 * width.length + 86 + 1,
        by omega, b,
        .ite_false (by simp [mid, hi, ha.outer, heq]) hb, ?_⟩
      simpa [mid, compared, updated, heq] using hbs
  obtain ⟨nb, hnb, b, hb, hbs⟩ := hbranch
  let cleared : Data := ⟨readRegs b.regs 0 1 none, clearStacks 9 b.stacks⟩
  have hclear := TupleProgram.clear_eval 9 (0 : Fin 8) 1 b
  have hreset := resetFlags_eval cleared
  refine ⟨nc + (nb + ((2 * (b.stacks 9).length + 3) + 3)), ?_, resetState cleared,
    hc.seq (hb.seq (hclear.seq hreset)), ?_, ?_, ?_, ?_⟩
  · have hb9 : b.stacks 9 = index := by simpa [hbs] using hi
    simp only [hi, ha.outer] at hnc
    rw [hb9]
    unfold callbackCost
    nlinarith
  · simp []
  · simp []
  · simp []
  · simp [ cleared, clearStacks, hbs]

theorem callback_contract (differences negatives : List Word) (width outer : Word)
    (frame : Fin 32 → Word)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length outer.length)
      (invariant differences negatives width outer frame)
      (effect differences negatives outer)
      (fun bits => bits.length < differences.length ∧ bits.length < negatives.length) := by
  intro bits tail base hvalid hbase
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  have ha : Ready differences negatives width outer a := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [a, RecordPrograms.state, ports] using hbase.1.differences
    · simpa [a, RecordPrograms.state, ports] using hbase.1.negatives
    · simpa [a, RecordPrograms.state, ports] using hbase.1.width
    · simpa [a, RecordPrograms.state, ports] using hbase.1.outer
    · intro j hj
      have h := hbase.1.empty j hj
      fin_cases j <;> simp_all [a, RecordPrograms.state, ports]
  obtain ⟨n, hn, b, hb, h5, h6, h7, hbs⟩ := callback_eval
    differences negatives width outer bits.reverse a ha rfl
    (by simpa using hvalid.1) (by simpa using hvalid.2) hds hns
  let next : Data := ⟨b.regs, Function.update base.stacks 21 (b.stacks 21)⟩
  have hnext : invariant differences negatives width outer frame next := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [next] using hbase.1.differences
    · simpa [next] using hbase.1.negatives
    · simpa [next] using hbase.1.width
    · simpa [next] using hbase.1.outer
    · intro j hj
      have h := hbase.1.empty j hj
      fin_cases j <;> simp_all [next]
    · intro j hj
      simpa [next, hj] using hbase.2 j hj
  have hend : b = RecordPrograms.state ports next false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp_all [ next, ports]
    · funext j
      rw [hbs]
      by_cases hj8 : j = 8 <;> by_cases hj9 : j = 9 <;> by_cases hj21 : j = 21 <;>
        simp_all [RecordPrograms.state, next, a, ports, Function.update_apply]
  refine ⟨n, next, ?_, hnext, ?_, ?_⟩
  · simpa [callbackCost] using hn
  · simp [effect, next, hbs, a, RecordPrograms.state, ports]
  · rw [← hend]
    exact hb

theorem unread_false (records : List Word) (suffix : Word) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa [RecordPrograms.unread] using ih

theorem any_false {α : Type*} (xs : List α) : xs.any (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

/-- Every record is parsed and processed by the fixed callback. The statement
records all preserved stacks, not only the emitted factor list. -/
theorem loop_eval (differences negatives : List Word) (width outer : Word)
    (records : List Word) (suffix : Word) (base : Data)
    (hbase : Ready differences negatives width outer base)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hrecords : ∀ bits ∈ records,
      bits.length < differences.length ∧ bits.length < negatives.length)
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length outer.length) records,
      ∃ next : Data,
        Eval loop n
          (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
          (RecordPrograms.state ports next false true false suffix []) ∧
        Ready differences negatives width outer next ∧
        next.stacks 21 = output differences negatives outer records (base.stacks 21) ∧
        (∀ j, j ≠ 21 → next.stacks j = base.stacks j) := by
  obtain ⟨n, next, hn, hnext, hv, he⟩ := RecordPrograms.iterate_run_with_on ports callback
    (fun _ => false) (callbackCost width.length outer.length)
    (invariant differences negatives width outer base.stacks)
    (effect differences negatives outer)
    (fun bits => bits.length < differences.length ∧ bits.length < negatives.length)
    (callback_contract differences negatives width outer base.stacks hds hns)
    records suffix base hrecords ⟨hbase, by intros; rfl⟩ v pr f
  refine ⟨n, hn, next, ?_, hnext.1, ?_, hnext.2⟩
  · simpa [loop, unread_false, any_false] using he
  · exact hv.fold_of_false (by intros; rfl) (fun a => a.stacks 21)
      (fun out bits => updated differences negatives outer bits.reverse out)
      (by intros; assumption)

theorem output_append (differences negatives : List Word) (outer : Word)
    (xs ys : List Word) (acc : Word) :
    output differences negatives outer (xs ++ ys) acc =
      output differences negatives outer ys (output differences negatives outer xs acc) := by
  simp [output, List.foldl_append]

/-- Descending traversal plus prepending restores the given ascending order.
The only discarded entry is the canonical unary word for the outer index. -/
theorem output_reverse_indices (differences negatives : List Word) (i : ℕ)
    (positions : List ℕ) (tail : List (UniversalRowProgram.Factor Word)) :
    output differences negatives (indexWord i) (positions.reverse.map indexWord)
        (Encoding.encodeList UniversalRowProgram.encodeFactor tail) =
      Encoding.encodeList UniversalRowProgram.encodeFactor
        (factors differences negatives i positions ++ tail) := by
  induction positions with
  | nil => simp [output, factors]
  | cons j rest ih =>
      rw [List.reverse_cons, List.map_append, output_append]
      change updated differences negatives (indexWord i) (indexWord j).reverse
        (output differences negatives (indexWord i) (rest.reverse.map indexWord)
          (Encoding.encodeList UniversalRowProgram.encodeFactor tail)) = _
      rw [ih]
      by_cases h : j = i <;>
        simp [updated, h, factors, prependFactor, Encoding.encodeList]

theorem loop_indices_eval_oai (differences negatives : List Word) (width : Word) (i : ℕ)
    (positions : List ℕ) (suffix : Word) (base : Data)
    (hbase : Ready differences negatives width (indexWord i) base)
    (hacc : base.stacks 21 = [false])
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length)
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length i)
        (positions.reverse.map indexWord), ∃ next : Data,
      Eval loop n
        (RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (positions.reverse.map indexWord) ++ suffix) [])
        (RecordPrograms.state ports next false true false suffix []) ∧
      Ready differences negatives width (indexWord i) next ∧
      next.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor
        (factors differences negatives i positions) ∧
      (∀ j, j ≠ 21 → next.stacks j = base.stacks j) := by
  have hv : ∀ bits ∈ positions.reverse.map indexWord,
      bits.length < differences.length ∧ bits.length < negatives.length := by
    intro bits hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    simpa using hpositions j (by simpa using hj)
  obtain ⟨n, hn, next, he, hr, ho, hf⟩ := loop_eval differences negatives width (indexWord i)
    (positions.reverse.map indexWord) suffix base hbase hds hns hv v pr f
  refine ⟨n, by simpa using hn, next, he, hr, ?_, hf⟩
  rw [ho, hacc]
  simpa [Encoding.encodeList] using output_reverse_indices differences negatives i positions []

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval_oai
