-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:25:00.694275+00:00
-- url     : https://prove2.me/submissions/6193f5aa-77e8-4cfe-9a33-f6d3d762dd53

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S132

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

theorem emitCurrent_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval emitCurrent (12*j+20) (data base regs j n out)
      (data base rf (j+1) n (true :: Encoding.frame (unary j) ++ out)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) := by
  let a := data base regs j n out
  let b := copied 5 1 a
  let c := selected b
  let d := emitted true (unary j) c
  let e := incremented 5 d
  have h1 := copy_eval 5 1 3 a (by decide) (by decide) (by decide) (by rfl)
  have h2 : Eval setSelected 1 b c := .base (.atom _ _)
  have h3 := emit_eval true (unary j) c
    (by simp [c, selected, b, copied, StackRoutines.copyStacks, a ])
    (by simp [c, selected])
  have h4 := increment_eval 5 d
  have he : e = data base e.regs (j+1) n (true :: Encoding.frame (unary j) ++ out) := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [ d, emitted, c, selected, b, copied,
      StackRoutines.copyStacks, a, List.replicate_succ]
  have h := h1.seq (h2.seq (h3.seq h4))
  change Eval emitCurrent _ a e at h
  rw [he] at h
  refine ⟨e.regs, ?_, ?_⟩
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [a, SubexpNormalizeProgram.emitIfSelectedSteps]
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have h4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    simp [e, incremented, d, emitted, c, selected, b, copied, readRegs, a, h0, h1, h4]

theorem tested_active (regs : Fin 10 → Bool) (n : ℕ) :
    testedRegs regs n 9 = decide (n ≠ 0) := by
  cases n <;> simp [testedRegs, readRegs, List.replicate_succ]

theorem peek_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval peek 1 (data base regs j n out) (data base (testedRegs regs n) j n out) := by
  exact .base (.atom _ _)

theorem pop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval pop 1 (data base regs j (n+1) out)
      (data base (readRegs regs 7 9 (some true)) j n out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (6 : Fin 10) 7 9)
    (data base regs j (n+1) out))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]

theorem loop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool)
    (hg : regs 9 = decide (n ≠ 0)) :
    ∃ rf, Eval loop (steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  induction n generalizing regs j out with
  | zero =>
      refine ⟨regs, ?_, by simpa using hg⟩
      simpa [steps, indexPrefix] using
        (Eval.while_false (body := .seq pop (.seq emitCurrent peek))
          (a := data base regs j 0 out) (show regs 9 = false by simpa using hg))
  | succ n ih =>
      obtain ⟨re, he, hr⟩ := emitCurrent_eval base (readRegs regs 7 9 (some true)) j n out
      have hp := pop_eval base regs j n out
      have ht := peek_eval base re (j+1) n (true :: Encoding.frame (unary j) ++ out)
      obtain ⟨rf, hf, hrf⟩ := ih (testedRegs re n) (j+1)
        (true :: Encoding.frame (unary j) ++ out) (tested_active re n)
      have h := Eval.while_true (show (data base regs j (n+1) out).regs 9 = true by simpa using hg)
        (hp.seq (he.seq ht)) hf
      refine ⟨rf, ?_, hrf⟩
      convert h using 1
      · simp only [steps]; omega
      · simp [indexPrefix, List.range'_succ, List.reverse_cons, List.flatMap_append,
          List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem command_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval command (1 + steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  obtain ⟨rf, h, hr⟩ := loop_eval base (testedRegs regs n) j n out (tested_active regs n)
  exact ⟨rf, (peek_eval base regs j n out).seq h, hr⟩

theorem program_trace (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Trace program (steps j n + 2)
      ((data base regs j n out).withPC (some program.entry))
      ((data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)).withPC none) := by
  obtain ⟨rf, h, _⟩ := command_eval base regs j n out
  refine ⟨rf, ?_⟩
  convert compiled_halt_trace h 5 7 using 1
  all_goals try with_reducible_and_instances rfl
  omega

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

theorem lookupPorts_injective (right : Bool) : Function.Injective (lookupPorts right) := by
  cases right <;> decide

theorem lookup_eval (right : Bool) (rows : List Word) (width index : Word) (a : Data)
    (ha : a.stacks (arrayPort right) = rows.flatten)
    (hw : a.stacks 3 = width) (hi : a.stacks 2 = index)
    (hindex : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (rowPort right) = [])
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval (lookup right) (index.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (afterLookup right (rows.getD index.length []) a) := by
  let inner : State 8 8 := ⟨a.regs, a.stacks ∘ lookupPorts right⟩
  have htake : (rows.take index.length).length = index.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindex)]
  have hrow : (rows.getD index.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact hrows _ (List.getElem_mem hindex)
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    (rows.take index.length) (rows.getD index.length [])
    (rows.drop (index.length + 1)).flatten width index inner.regs inner.stacks
    (by simpa [inner, lookupPorts] using ha.trans (GatherProgram.row_decomposition rows _ hindex))
    (by simpa [inner, lookupPorts] using hw) (by simpa [inner, lookupPorts] using hi)
    htake.symm (fun row hr => hrows row (List.mem_of_mem_take hr)) hrow
    (by simpa [inner, lookupPorts] using h4) (by simpa [inner, lookupPorts] using h5)
    (by simpa [inner, lookupPorts] using h6) (by simpa [inner, lookupPorts] using h7)
  have hin : embedState id (lookupPorts right) a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (lookupPorts_injective right)
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout' : embedState id (lookupPorts right) a
      ⟨readRegs inner.regs 0 1 none,
        ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩ =
      afterLookup right (rows.getD index.length []) a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (lookupPorts_injective right)
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j; cases right <;> fin_cases j <;>
        simp_all [ inner, lookupPorts, rowPort, arrayPort, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      have hr : j ≠ rowPort right := fun h => hj ⟨1, h.symm⟩
      simp [ h2, hr]
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (lookupPorts right) a Function.injective_id (lookupPorts_injective right)
    (a := inner)
    (b := ⟨readRegs inner.regs 0 1 none,
      ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩) ht
  simpa only [hin, hout', htake, lookup] using he

theorem copyIndex_eval (a : Data) (h15 : a.stacks 15 = []) :
    Eval copyIndex (7 * (a.stacks 9).length + 5) a (afterCopy a) :=
  TupleProgram.copy_eval 9 2 15 (0 : Fin 8) 1 (by decide) (by decide) (by decide)
    (by decide) a h15

theorem equalityRegs_injective : Function.Injective equalityRegs := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem equalityStacks_injective : Function.Injective equalityStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (afterEquality a (decide (a.stacks 1 = a.stacks 12))) := by
  let inner : State 5 13 :=
    ⟨a.regs ∘ equalityRegs, a.stacks ∘ equalityStacks⟩
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
    · intro j; fin_cases j <;> norm_num [afterEquality, CollisionStreamProgram.sealed, equalityRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro j
      fin_cases j <;>
        simp [ CollisionStreamProgram.sealed, inner, equalityStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityInner equalityRegs equalityStacks a
    equalityRegs_injective equalityStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · have hn' : n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 := by
      simpa [inner, equalityStacks] using hn
    omega
  · simpa only [hin, hout, equality] using he

theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (left right width source payload acc output source' width' acc' payload' : Word) :
    embedState emitRegs emitStacks (state regs left right width source payload acc output)
      (SubexpNormalizeProgram.filterState v p f source' width' acc' payload') =
      state (flags regs v p f) left right width' source' payload' acc' output := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStacks_injective
  · intro j; fin_cases j <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
    have h7 : j ≠ 7 := fun h => hj ⟨2, h.symm⟩
    simp [ flags, h0, h1, h7]
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h8 : j ≠ 8 := fun h => hj ⟨0, h.symm⟩
    have h3 : j ≠ 3 := fun h => hj ⟨1, h.symm⟩
    have h13 : j ≠ 13 := fun h => hj ⟨2, h.symm⟩
    have h9 : j ≠ 9 := fun h => hj ⟨3, h.symm⟩
    fin_cases j <;> simp_all []

theorem emit_eval (bits left right width source acc output : Word) (regs : Regs) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 7) bits + 1)
      (state regs left right width source bits.reverse acc output)
      (state (flags regs false true false) left right width source []
        (if regs 7 then true :: (Encoding.frame bits ++ acc) else acc) output) := by
  have ht := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks
    (state regs left right width source bits.reverse acc output) emitRegs_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 7) bits source width acc (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using ht

theorem markDifferent_eval (regs : Regs) (answer : Bool)
    (left right width source payload acc output : Word) :
    Eval markDifferent 2
      ⟨regs, Function.update (state regs left right width source payload acc output).stacks 11 [answer]⟩
      (state (markedRegs regs answer) left right width source payload acc output) := by
  let a : Data := ⟨regs, Function.update (state regs left right width source payload acc output).stacks 11 [answer]⟩
  let b := (StructuredProgram.Atom.pop (11 : Fin 16) (7 : Fin 8) 1).eval a
  have h1 : Eval (RecordPrograms.atom (.pop 11 7 1)) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (7 : Fin 8) 7) b)
  have ht := h1.seq h2
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; fin_cases j <;> simp [a, b, markedRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, readRegs]
  · funext j; fin_cases j <;> simp [a, b, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr]

theorem callback_eval (left right : List Word) (width bits source acc output : Word) (regs : Regs)
    (hl : bits.length < left.length) (hr : bits.length < right.length)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length) :
    ∃ n ≤ callbackCost width.length bits, ∃ rf : Regs,
      rf 5 = regs 5 ∧ rf 6 = regs 6 ∧ rf 7 = false ∧
      Eval callback n (state regs left.flatten right.flatten width source bits.reverse acc output)
        (state rf left.flatten right.flatten width source []
          (if keep left right bits then true :: (Encoding.frame bits ++ acc) else acc) output) := by
  let a := state regs left.flatten right.flatten width source bits.reverse acc output
  let a1 := afterCopy a
  let a2 := afterLookup false (left.getD bits.length []) a1
  let a3 := afterCopy a2
  let a4 := afterLookup true (right.getD bits.length []) a3
  have h1 := copyIndex_eval a (by rfl)
  have h2 := lookup_eval false left width bits.reverse a1
    (by simp [a1, afterCopy, copyStacks, a, arrayPort])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simpa using hl) hleft
    (by simp [a1, afterCopy, copyStacks, a, rowPort])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
  have h3 := copyIndex_eval a2 (by simp [a2, a1, afterCopy, copyStacks, a, rowPort])
  have h4 := lookup_eval true right width bits.reverse a3
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, arrayPort, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simpa using hr) hright
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
  simp only [List.length_reverse] at h2 h4
  obtain ⟨ne, hne, he⟩ := equality_eval a4
  let answer := decide (left.getD bits.length [] = right.getD bits.length [])
  let re : Regs := fun j => if j.val < 5 then false else regs j
  have heout : afterEquality a4 (decide (a4.stacks 1 = a4.stacks 12)) =
      (⟨re, Function.update (state re left.flatten right.flatten width source bits.reverse acc output).stacks
        11 [answer]⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> norm_num [afterEquality, a4, a3, a2, a1, a, afterCopy,
        afterLookup, readRegs, state, re]
    · funext j; fin_cases j <;> simp [ a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort, answer]
  rw [heout] at he
  have hm := markDifferent_eval re answer left.flatten right.flatten width source bits.reverse acc output
  have hem := emit_eval bits left.flatten right.flatten width source acc output (markedRegs re answer)
  have hkeep : markedRegs re answer 7 = keep left right bits := by
    simp [markedRegs, answer, keep]
  rw [hkeep] at hem
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (he.seq (hm.seq hem)))))
  have hllen : (left.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hl]; exact hleft _ (List.getElem_mem hl)
  have hrlen : (right.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hr]; exact hright _ (List.getElem_mem hr)
  let readCost := bits.length * (14 * width.length + 10) + 15 * width.length + 16
  let total := 7 * bits.length + 5 + (readCost +
    (7 * bits.length + 5 + (readCost +
      (ne + (2 + (SubexpNormalizeProgram.emitIfSelectedSteps (keep left right bits) bits + 1))))))
  refine ⟨total, ?_, flags (markedRegs re answer) false true false, ?_, ?_, ?_, ?_⟩
  · have hb := SubexpNormalizeProgram.emitIfSelected_steps_le (keep left right bits) bits
    have hleftRow : a4.stacks 1 = left.getD bits.length [] := by
      simp [a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort]
    have hrightRow : a4.stacks 12 = right.getD bits.length [] := by
      simp [a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort]
    rw [hleftRow, hrightRow, hllen, hrlen] at hne
    dsimp [callbackCost, total, readCost]
    nlinarith
  · change (if (5 : ℕ) < 5 then false else regs 5) = regs 5
    rfl
  · change (if (6 : ℕ) < 5 then false else regs 6) = regs 6
    rfl
  · simp [flags]
  · simpa [callback, total, readCost, a2, a1, a, afterLookup, afterCopy,
      copyStacks, rowPort, state] using ht

theorem recordState_state (regs : Regs) (v p f : Bool)
    (left right width source payload acc output source' payload' : Word) :
    RecordPrograms.state ports (state regs left right width source payload acc output)
      v p f source' payload' =
      state (outerFlags regs v p f) left right width source' payload' acc output := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j; fin_cases j <;> simp [ ports ]

theorem callback_contract (left right : List Word) (width : Word)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length) (invariant left right width)
      (SubexpNormalizeProgram.FilterEffect 13 (keep left right))
      (fun bits => bits.length < left.length ∧ bits.length < right.length) := by
  intro bits tail base hvalid hinv
  obtain ⟨regs, source, payload, acc, rfl⟩ := hinv
  obtain ⟨n, hn, rf, h5, h6, h7, he⟩ := callback_eval left right width bits tail acc []
    (outerFlags regs false true false) hvalid.1 hvalid.2 hleft hright
  let next := state rf left.flatten right.flatten width tail []
    (if keep left right bits then true :: (Encoding.frame bits ++ acc) else acc) []
  have hnext : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · simpa [next, state, ports, outerFlags] using h5
    · simpa [next, state, ports, outerFlags] using h6
    · exact h7
    · rfl
    · rfl
  refine ⟨n, next, hn, ⟨rf, tail, [], _, rfl⟩, ?_, ?_⟩
  · rfl
  · rw [hnext, recordState_state]
    exact he

theorem filter_eval (left right : List Word) (width : Word) (records : List Word) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ bits ∈ records, bits.length < left.length ∧ bits.length < right.length) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length) records, ∃ rf : Regs,
      Eval (RecordPrograms.iterate ports callback) n
        (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [false] [])
        (state rf left.flatten right.flatten width [] []
          (Encoding.encodeList id (records.filter (keep left right)).reverse) []) := by
  let base := state regs left.flatten right.flatten width
    (Encoding.encodeList id records) [] [false] []
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost width.length) (invariant left right width)
    (SubexpNormalizeProgram.FilterEffect 13 (keep left right))
    (fun bits => bits.length < left.length ∧ bits.length < right.length)
    (callback_contract left right width hleft hright) records [] base hvalid
    ⟨regs, _, [], [false], rfl⟩ (regs 5) (regs 6) (regs 7)
  have hout := SubexpNormalizeProgram.filterVisits_result 13 (keep left right) history [] rfl
  obtain ⟨rr, source, payload, acc, rfl⟩ := hnext
  have hacc : acc = Encoding.encodeList id (records.filter (keep left right)).reverse := by
    simpa [state] using hout
  rw [hacc] at he
  have hany : records.any (fun _ => false) = false := by induction records <;> simp_all
  have hunread : RecordPrograms.unread (fun _ => false) records [] = [] := by
    induction records <;> simp_all [RecordPrograms.unread]
  refine ⟨n, hn, outerFlags rr false true false, ?_⟩
  simpa only [base, List.append_nil, hany, hunread, recordState_state, outerFlags_self] using he

theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

private theorem embed_reverse (regs : Regs) (v p f : Bool)
    (left right width source payload acc output acc' width' out' payload' : Word) :
    embedState emitRegs reverseStacks (state regs left right width source payload acc output)
      (SubexpNormalizeProgram.filterState v p f acc' width' out' payload') =
      state (flags regs v p f) left right width' source payload' acc' out' := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective reverseStacks_injective
  · intro j; fin_cases j <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
    have h7 : j ≠ 7 := fun h => hj ⟨2, h.symm⟩
    simp [ flags, h0, h1, h7]
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h13 : j ≠ 13 := fun h => hj ⟨0, h.symm⟩
    have h3 : j ≠ 3 := fun h => hj ⟨1, h.symm⟩
    have h14 : j ≠ 14 := fun h => hj ⟨2, h.symm⟩
    have h9 : j ≠ 9 := fun h => hj ⟨3, h.symm⟩
    fin_cases j <;> simp_all []

theorem reverse_eval (records : List Word) (left right width source : Word) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval reverseCall n
        (state regs left right width source [] (Encoding.encodeList id records) [false])
        (state (flags regs false true false) left right width source [] []
          (Encoding.encodeList id records.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] width
    (regs 0) (regs 1) (regs 7)
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStacks
    (state regs left right width source [] (Encoding.encodeList id records) [false])
    emitRegs_injective reverseStacks_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [List.append_nil, Encoding.encodeList, embed_reverse, flags_self, reverseCall] using he

theorem initialize_eval (dst : Fin 16) (a : Data) :
    Eval (initializeList dst) 2 a
      ⟨Function.update a.regs 0 false, Function.update a.stacks dst (false :: a.stacks dst)⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst (0 : Fin 8))
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval a))
  exact h1.seq h2

theorem encoded_filter_length_le (records : List Word) (test : Word → Bool) :
    (Encoding.encodeList id (records.filter test)).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons b bs ih =>
      cases h : test b <;> simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem command_eval (left right : List Word) (width : Word) (records : List Word) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ bits ∈ records, bits.length < left.length ∧ bits.length < right.length) :
    ∃ n, n + 1 ≤ sourceBound width.length records ∧ ∃ rf : Regs,
      Eval command n
        (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
        (state rf left.flatten right.flatten width [] [] []
          (Encoding.encodeList id (records.filter (keep left right)))) := by
  obtain ⟨n, hn, rf, he⟩ := filter_eval left right width records (Function.update regs 0 false)
    hleft hright hvalid
  obtain ⟨m, hm, hr⟩ := reverse_eval (records.filter (keep left right)).reverse
    left.flatten right.flatten width [] (Function.update rf 0 false)
  rw [List.reverse_reverse] at hr
  have hi := initialize_eval 13
    (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
  have ho := initialize_eval 14
    (state rf left.flatten right.flatten width [] []
      (Encoding.encodeList id (records.filter (keep left right)).reverse) [])
  have hi' : Eval (initializeList 13) 2
      (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
      (state (Function.update regs 0 false) left.flatten right.flatten width
        (Encoding.encodeList id records) [] [false] []) := by
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp []
  have ho' : Eval (initializeList 14) 2
      (state rf left.flatten right.flatten width [] []
        (Encoding.encodeList id (records.filter (keep left right)).reverse) [])
      (state (Function.update rf 0 false) left.flatten right.flatten width [] []
        (Encoding.encodeList id (records.filter (keep left right)).reverse) [false]) := by
    convert ho using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp []
  have hlen : (Encoding.encodeList id (records.filter (keep left right)).reverse).length ≤
      (Encoding.encodeList id records).length := by
    have hrev := ProgramEncoding.encodeRecords_length (records.filter (keep left right)).reverse
    have horig := ProgramEncoding.encodeRecords_length (records.filter (keep left right))
    have hf := encoded_filter_length_le records (keep left right)
    have hsame : (Encoding.encodeList id (records.filter (keep left right)).reverse).length =
        (Encoding.encodeList id (records.filter (keep left right))).length := by
      change (ProgramEncoding.encodeRecords _).length = (ProgramEncoding.encodeRecords _).length
      rw [hrev, horig]
      simp
    exact hsame.le.trans hf
  refine ⟨_, ?_, flags (Function.update rf 0 false) false true false, hi'.seq (he.seq (ho'.seq hr))⟩
  dsimp [sourceBound]
  omega

theorem filter_indexRecords (left right : List Word) (positions : List ℕ) :
    (indexRecords positions).filter (keep left right) = indexRecords (mismatch left right positions) := by
  simp [indexRecords, mismatch, List.filter_map, keep, Function.comp_def]

theorem program_runsIn (left right : List Word) (width : Word) (positions : List ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ i ∈ positions, i < left.length ∧ i < right.length) :
    ∃ rf : Regs, RunsIn program (sourceBound width.length (indexRecords positions))
      ((state regs left.flatten right.flatten width
        (ProgramEncoding.encodeRecords (indexRecords positions)) [] [] []).withPC (some program.entry))
      ((state rf left.flatten right.flatten width [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval left right width (indexRecords positions) regs hleft hright
    (by intro bits hb; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; simpa using hvalid i hi)
  rw [filter_indexRecords] at he
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 8 14⟩

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mismatch filter on the exact one-hot word representation. -/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls MulticolorTypes

theorem oneHot_injective {r : ℕ} : Function.Injective (@oneHot r) := by
  intro a b h
  have hh := congrFun (List.ofFn_inj.mp h) a
  have hb : b = a := by simpa [oneHot] using hh.symm
  exact hb.symm

theorem colorRows_width {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    ∀ row ∈ colorRows w, row.length = r := by
  intro row hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  simp [oneHot]

theorem colorRows_flatten {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    (colorRows w).flatten = ReadPlan.encodeWord w := rfl

theorem mismatch_range {r Q : ℕ} (left right : MulticolorTypes.Word r Q) :
    mismatch (colorRows left) (colorRows right) (List.range Q) = selectedPositions left right := by
  rw [mismatch, ← List.map_coe_finRange, List.filter_map]
  unfold selectedPositions
  congr 1
  apply List.filter_congr
  intro i hi
  simp [colorRows, oneHot_injective.eq_iff]

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords mismatch)

theorem rangeMap_injective : Function.Injective rangeMap := by decide

theorem indexPrefix_eq (positions : List ℕ) :
    SubexpUnaryRangeProgram.indexPrefix positions ++ [false] =
      ProgramEncoding.encodeRecords (indexRecords positions) := by
  induction positions with
  | nil => rfl
  | cons i is ih =>
      simpa [SubexpUnaryRangeProgram.indexPrefix, indexRecords,
        ProgramEncoding.encodeRecords, Encoding.encodeList, List.append_assoc] using
        congrArg (fun tail => true :: (Encoding.frame (List.replicate i true) ++ tail)) ih

theorem rangeCall_eval (left right width count out : Word) (regs : Regs) (j n : ℕ) :
    ∃ rf : Regs, Eval rangeCall (SubexpUnaryRangeProgram.steps j n + 2)
      (state regs left right width count (List.replicate j true) (List.replicate n true) out [])
      (state rf left right width count (List.replicate (j + n) true) []
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out) []) := by
  let a := state regs left right width count (List.replicate j true) (List.replicate n true) out []
  let base : SubexpUnaryRangeProgram.Data := ⟨regs, a.stacks ∘ rangeMap⟩
  obtain ⟨rf, ht⟩ := SubexpUnaryRangeProgram.program_trace base regs j n out
  have hin : embedState id rangeMap a (SubexpUnaryRangeProgram.data base regs j n out) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rangeMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k; fin_cases k <;> rfl
    · intros; rfl
  have hout : embedState id rangeMap a
      (SubexpUnaryRangeProgram.data base rf (j + n) 0
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out)) =
      state rf left right width count (List.replicate (j + n) true) []
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rangeMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k; fin_cases k <;> rfl
    · intro k hk
      have h5 : k ≠ 5 := fun h => hk ⟨5, by simpa [rangeMap] using h.symm⟩
      have h6 : k ≠ 6 := fun h => hk ⟨6, by simpa [rangeMap] using h.symm⟩
      have h8 : k ≠ 8 := fun h => hk ⟨7, by simpa [rangeMap] using h.symm⟩
      fin_cases k <;> simp_all [state, a]
  have he := eval_call_lifted SubexpUnaryRangeProgram.program id rangeMap a
    Function.injective_id rangeMap_injective ht
  exact ⟨rf, by simpa only [rangeCall, hin, hout] using he⟩

theorem filterCall_eval (left right : List Word) (width count : Word)
    (positions : List ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ i ∈ positions, i < left.length ∧ i < right.length) :
    ∃ n ≤ MismatchPlanProgram.sourceBound width.length (indexRecords positions), ∃ rf : Regs,
      Eval filterCall n
        (state regs left.flatten right.flatten width count [] []
          (ProgramEncoding.encodeRecords (indexRecords positions)) [])
        (state rf left.flatten right.flatten width count [] [] []
          (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))) := by
  let a := state regs left.flatten right.flatten width count [] []
    (ProgramEncoding.encodeRecords (indexRecords positions)) []
  obtain ⟨rf, n, hn, ht⟩ := MismatchPlanProgram.program_runsIn left right width positions
    (regs ∘ filterRegs) hleft hright hvalid
  have hin : embedState filterRegs filterStacks a
      (MismatchPlanProgram.state (regs ∘ filterRegs) left.flatten right.flatten width
        (ProgramEncoding.encodeRecords (indexRecords positions)) [] [] []) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1)
    · intros; rfl
    · intros; rfl
    · intro k; fin_cases k <;> rfl
    · intros; rfl
  have hout : embedState filterRegs filterStacks a
      (MismatchPlanProgram.state rf left.flatten right.flatten width [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))) =
      state (installedRegs regs rf) left.flatten right.flatten width count [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions))) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1)
    · intro k; simp [installedRegs, k.isLt, state ]
    · intro k hk
      have hge : ¬ k.val < 8 := by
        intro h; exact hk ⟨⟨k.val, h⟩, Fin.ext rfl⟩
      simp [installedRegs, state, a, hge]
    · intro k; fin_cases k <;> rfl
    · intro k hk
      have h8 : k ≠ 8 := fun h => hk ⟨8, h.symm⟩
      have h14 : k ≠ 14 := fun h => hk ⟨14, h.symm⟩
      fin_cases k <;> simp_all [state, a]
  have he := eval_call_lifted MismatchPlanProgram.program filterRegs filterStacks a
    (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1) ht
  exact ⟨n, hn, installedRegs regs rf, by simpa only [filterCall, hin, hout] using he⟩

theorem command_eval (left right : List Word) (width : Word) (q : ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hql : q ≤ left.length) (hqr : q ≤ right.length) :
    ∃ n, n + 1 ≤ budget q width.length ∧ ∃ rf : Regs,
      Eval command n
        (state regs left.flatten right.flatten width (List.replicate q true) [] [] [] [])
        (state rf left.flatten right.flatten width (List.replicate q true) [] [] []
          (ProgramEncoding.encodeRecords (indexRecords (mismatch left right (List.range q).reverse)))) := by
  let a := state regs left.flatten right.flatten width (List.replicate q true) [] [] [] []
  let rc := readRegs regs 0 1 none
  let ri := Function.update rc 0 false
  have hc : Eval (.call (copyProgram 16 6 15 (0 : Fin 10) 1)) (7 * q + 5) a
      (state rc left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [] []) := by
    have h := TupleProgram.copy_eval 16 6 15 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
    convert h using 1
    · simp [a, state]
    · apply congrArg (StructuredProgram.State.mk rc)
      funext k; fin_cases k <;> simp [a, state, copyStacks]
  have hi : Eval initializeSource 2
      (state rc left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [] [])
      (state ri left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [false] []) := by
    have h := Eval.seq
      (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) false)
        (state rc left.flatten right.flatten width (List.replicate q true) []
          (List.replicate q true) [] [])))
      (Eval.base (StructuredProgram.Eval.atom (.push (8 : Fin 17) (0 : Fin 10))
        ((StructuredProgram.Atom.set (0 : Fin 10) false).eval
          (state rc left.flatten right.flatten width (List.replicate q true) []
            (List.replicate q true) [] []))))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext k; fin_cases k <;> simp [state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  obtain ⟨rr, hr⟩ := rangeCall_eval left.flatten right.flatten width (List.replicate q true)
    [false] ri 0 q
  have hprefix : SubexpUnaryRangeProgram.indexPrefix (List.range' 0 q).reverse ++ [false] =
      ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse) := by
    rw [← List.range_eq_range']
    exact indexPrefix_eq (List.range q).reverse
  simp only [List.replicate_zero, Nat.zero_add, hprefix] at hr
  let afterRange := state rr left.flatten right.flatten width (List.replicate q true)
    (List.replicate q true) [] (ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse)) []
  have hclear : Eval (.call (clearProgram 5 (0 : Fin 10) 1)) (2 * q + 3) afterRange
      (state (readRegs rr 0 1 none) left.flatten right.flatten width (List.replicate q true)
        [] [] (ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse)) []) := by
    have h := TupleProgram.clear_eval 5 (0 : Fin 10) 1 afterRange
    convert h using 1
    · simp [afterRange, state]
    · apply congrArg (StructuredProgram.State.mk (readRegs rr 0 1 none))
      funext k; fin_cases k <;> simp [afterRange, state, clearStacks]
  obtain ⟨nf, hnf, rf, hf⟩ := filterCall_eval left right width (List.replicate q true)
    (List.range q).reverse (readRegs rr 0 1 none) hleft hright (by
      intro i hi
      have hiq : i < q := List.mem_range.mp (List.mem_reverse.mp hi)
      exact ⟨lt_of_lt_of_le hiq hql, lt_of_lt_of_le hiq hqr⟩)
  refine ⟨_, ?_, rf, hc.seq (hi.seq (hr.seq (hclear.seq hf)))⟩
  dsimp [budget]
  omega

theorem program_runsIn (left right : List Word) (width : Word) (q : ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hql : q ≤ left.length) (hqr : q ≤ right.length) :
    ∃ rf : Regs, RunsIn program (budget q width.length)
      ((state regs left.flatten right.flatten width (List.replicate q true) [] [] [] []).withPC
        (some program.entry))
      ((state rf left.flatten right.flatten width (List.replicate q true) [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right (List.range q).reverse)))).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval left right width q regs hleft hright hql hqr
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 16 14⟩

theorem word_program_runsIn {r Q : ℕ} (left right : MulticolorTypes.Word r Q) (regs : Regs) :
    ∃ rf : Regs, RunsIn program (budget Q r)
      ((state regs (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) (List.replicate Q true) [] [] [] []).withPC (some program.entry))
      ((state rf (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) (List.replicate Q true) [] [] []
        (ProgramEncoding.encodeRecords (indexRecords
          (MismatchPlanProgram.selectedPositions left right).reverse))).withPC none) := by
  obtain ⟨rf, ht⟩ := program_runsIn (MismatchPlanProgram.colorRows left)
    (MismatchPlanProgram.colorRows right) (List.replicate r true) Q regs
    (by simpa using MismatchPlanProgram.colorRows_width left)
    (by simpa using MismatchPlanProgram.colorRows_width right) (by simp) (by simp)
  refine ⟨rf, ?_⟩
  have hreverse : mismatch (MismatchPlanProgram.colorRows left) (MismatchPlanProgram.colorRows right)
      (List.range Q).reverse = (MismatchPlanProgram.selectedPositions left right).reverse := by
    rw [mismatch, List.filter_reverse, ← mismatch, MismatchPlanProgram.mismatch_range]
  simpa only [List.length_replicate, MismatchPlanProgram.colorRows_flatten, hreverse] using ht

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

theorem filterStacks_injective : Function.Injective filterStacks := by decide

variable {r Q Δ : ℕ}

theorem filter_eval_oai (left right : MulticolorTypes.Word r Q) (a : Data)
    (hl : a.stacks 19 = ReadPlan.encodeWord left)
    (hr : a.stacks 18 = ReadPlan.encodeWord right)
    (hw : a.stacks 21 = List.replicate r true)
    (hq : a.stacks 22 = List.replicate Q true)
    (he : ∀ j : Fin 49, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 45] → a.stacks j = []) :
    ∃ n ≤ UniversalRowMismatchProgram.budget Q r, ∃ b : Data,
      Eval filter n a b ∧ b.stacks = Function.update a.stacks 45
        (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
          (MismatchPlanProgram.selectedPositions left right).reverse)) := by
  let first := UniversalRowMismatchProgram.state a.regs (ReadPlan.encodeWord left)
    (ReadPlan.encodeWord right) (List.replicate r true) (List.replicate Q true) [] [] [] []
  obtain ⟨rf, n, hn, ht⟩ := UniversalRowMismatchProgram.word_program_runsIn left right a.regs
  let result := ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
    (MismatchPlanProgram.selectedPositions left right).reverse)
  let last := UniversalRowMismatchProgram.state rf (ReadPlan.encodeWord left)
    (ReadPlan.encodeWord right) (List.replicate r true) (List.replicate Q true) [] [] [] result
  have hports : ∀ k : Fin 17, a.stacks (filterStacks k) = first.stacks k := by
    intro k
    fin_cases k <;> simp [first, UniversalRowMismatchProgram.state, filterStacks, hl, hr, hw, hq,
      he 0 (by simp), he 1 (by simp), he 2 (by simp), he 3 (by simp), he 4 (by simp),
      he 5 (by simp), he 6 (by simp), he 7 (by simp), he 8 (by simp), he 9 (by simp),
      he 10 (by simp), he 11 (by simp), he 45 (by simp)]
  have hin : embedState id filterStacks a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id filterStacks_injective
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro k; exact hports k
    · intros; rfl
  let b := embedState id filterStacks a last
  have ht' : Eval filter n a b := by
    have h := eval_call_lifted UniversalRowMismatchProgram.program id filterStacks a
      Function.injective_id filterStacks_injective (a := first) (b := last) ht
    simpa only [filter, b, hin] using h
  refine ⟨n, hn, b, ht', ?_⟩
  funext j
  by_cases hj : ∃ k, filterStacks k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (filterStacks k) = last.stacks k from
      embedState_stack _ _ _ _ filterStacks_injective k]
    have hk := hports k
    fin_cases k <;> first
      | rfl
      | simpa [last, first, UniversalRowMismatchProgram.state, filterStacks, result] using hk.symm
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h45 : j ≠ 45 := fun h => hj ⟨14, h.symm⟩
    simp [h45]

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval_oai
