-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:09:50.616811+00:00
-- url     : https://prove2.me/submissions/f4270ec7-60ed-4c43-b209-8d39b7956c71

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S097

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

theorem low_injective : Function.Injective low := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 29 => k.val) h)

theorem embed_input (a : Data) :
    embedState id low a ⟨a.regs, a.stacks ∘ low⟩ = a := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem read_eval (a : Data) (before : List (List Bool)) (row rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval read (before.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (readResult a row) := by
  let b : State 8 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.readStacks row (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    before row rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hw rfl hi hb hr h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hf : embedState id low a b = readResult a row := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [ b, low, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [ h1, h2]
  simpa only [embed_input, hf, read] using he

theorem replace_eval (a : Data) (before : List (List Bool))
    (row newRow rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hn : a.stacks 1 = newRow) (hw : a.stacks 3 = width)
    (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length)
    (hr : row.length = width.length) (hnew : newRow.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval replace (before.length * (14 * width.length + 10) + 20 * width.length + 21)
      a (replaceResult a (before.flatten ++ (newRow ++ rest))) := by
  let b : State 8 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.replaceStacks before newRow rest (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 8) 1 (by decide)
    before row newRow rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hn hw rfl hi hb hr hnew h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hf : embedState id low a b =
      replaceResult a (before.flatten ++ (newRow ++ rest)) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [ b, low, ArrayUpdatePrograms.replaceStacks]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [ h0, h2]
  simpa only [embed_input, hf, replace] using he

theorem copy_eval (a : Data) (src dst : Fin 29) (hsd : src ≠ dst)
    (hs8 : src ≠ 8) (h8d : (8 : Fin 29) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 8 (0 : Fin 8) 1 hsd hs8 h8d (by decide) a h8

theorem clear_eval (a : Data) (src : Fin 29) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 8) 1 a.regs a.stacks)
    2 rfl rfl
  simpa [clear, cleared, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

theorem eqRegs_injective : Function.Injective eqRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem eqPorts_injective : Function.Injective eqPorts := by
  decide

theorem equality_eval (a : Data) (h11 : a.stacks 11 = []) :
    ∃ n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 22,
      Eval equality n a (compared a (decide (a.stacks 0 = a.stacks 28))) := by
  let x : State 5 13 := ⟨a.regs ∘ eqRegs, a.stacks ∘ eqPorts⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  let y := CollisionStreamProgram.sealed x (decide (a.stacks 0 = a.stacks 28))
  let mid : Data :=
    ⟨fun j => if j.val < 5 then false else a.regs j,
      Function.update (Function.update (Function.update a.stacks 0 []) 28 [])
        11 [decide (a.stacks 0 = a.stacks 28)]⟩
  have hx : embedState eqRegs eqPorts a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState eqRegs eqPorts a y = mid := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intro i
      change (if i.val < 5 then false else a.regs (eqRegs i)) = false
      simp [i.isLt]
    · intro j hj
      have hge : ¬ j.val < 5 := fun h => hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [mid, hge]
    · intro i
      by_cases hi1 : i = 1
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi12 : i = 12
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi11 : i = 11
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      have h0 : eqPorts i ≠ 0 := fun h => hi1 (eqPorts_injective (h.trans eqPorts_one.symm))
      have h28 : eqPorts i ≠ 28 := fun h => hi12 (eqPorts_injective (h.trans eqPorts_twelve.symm))
      have h11' : eqPorts i ≠ 11 := fun h => hi11 (eqPorts_injective (h.trans eqPorts_eleven.symm))
      simp [mid, y, x, CollisionStreamProgram.sealed, hi1, hi12, hi11, h0, h28, h11']
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨1, h.symm⟩
      have h28 : j ≠ 28 := fun h => hj ⟨12, h.symm⟩
      have h11' : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      simp [mid, h0, h28, h11']
  have ht' : Trace equalityInner (n + 1) (x.withPC (some equalityInner.entry))
      (y.withPC none) := by
    simpa [equalityInner, y, x, Function.comp_def, eqPorts] using
      compiled_halt_trace ht (1 : Fin 13) 11
  have hl := eval_call_lifted equalityInner eqRegs eqPorts a
    eqRegs_injective eqPorts_injective ht'
  have hl' : Eval (.call (ProgramLinking.liftProgram equalityInner eqRegs eqPorts))
      (n + 1) a mid := by
    simpa only [hx, hy] using hl
  have hf : (StructuredProgram.Atom.set (0 : Fin 8) false).eval
      ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid) =
      compared a (decide (a.stacks 0 = a.stacks 28)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj0 : j = 0
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      by_cases hj7 : j = 7
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      simp [mid, readRegs, hj0, hj7, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · funext j; by_cases hj : j = 11 <;>
        simp [mid, hj, h11, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  have he := hl'.seq
    ((Eval.base (StructuredProgram.Eval.atom (.pop (11 : Fin 29) (7 : Fin 8) 0) mid)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false)
        ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid))))
  rw [hf] at he
  refine ⟨n + 1 + (1 + 1), ?_, he⟩
  change n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 19 at hn
  omega

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

open BitProgram StructuredCalls StackRoutines MatrixInputAccess


theorem extract_eval (a : Data) (second : Bool)
    (head slot width : List Bool) (before after : List (List Bool))
    (hwork : WorkReady a) (h0 : a.stacks 0 = [])
    (hhead : a.stacks (headPort second) = []) (hslot : a.stacks (slotPort second) = [])
    (hsource : a.stacks (sourcePort second) = head ++ before.flatten ++ (slot ++ after.flatten))
    (hw : a.stacks 3 = width) (hi : (a.stacks 25).length = before.length + 1)
    (hh : head.length = width.length) (hs : slot.length = width.length)
    (hb : ∀ row ∈ before, row.length = width.length) :
    Eval (extract second)
      (7 * (a.stacks (sourcePort second)).length +
        (before.length + 1) * (14 * width.length + 17) + 48 * width.length + 58)
      a (extracted a second head slot) := by
  rcases hwork with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  let a1 := copied a (sourcePort second) 0
  let a2 := readResult a1 head
  let a3 := copied a2 1 (headPort second)
  let a4 := cleared a3 1
  let a5 := copied a4 25 2
  let a6 := readResult a5 slot
  let a7 := copied a6 1 (slotPort second)
  have t0 := copy_eval a (sourcePort second) 0
    (by cases second <;> decide) (by cases second <;> decide) (by decide) h8
  have t1 := read_eval a1 [] head (before.flatten ++ (slot ++ after.flatten)) width
    (by simp [a1, copyStacks, h0, hsource, List.append_assoc])
    (by simpa [a1, copied, copyStacks] using hw)
    (by simp [a1, copyStacks, h2]) (by simp) hh
    (by simpa [a1, copied, copyStacks] using h4)
    (by simpa [a1, copied, copyStacks] using h5)
    (by simpa [a1, copied, copyStacks] using h6)
    (by simpa [a1, copied, copyStacks] using h7)
  have t2 := copy_eval a2 1 (headPort second)
    (by cases second <;> decide) (by decide) (by cases second <;> decide)
    (by simp [a2, a1, copyStacks, h8])
  have t3 := clear_eval a3 1
  have t4 := copy_eval a4 25 2 (by decide) (by decide) (by decide)
    (by cases second <;> simp [a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h8])
  have t5 := read_eval a5 (head :: before) slot after.flatten width
    (by cases second <;> simp [a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h0, hsource, List.append_assoc])
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using hw)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using hi)
    (by simpa [hh] using hb) hs
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h4)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h5)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h6)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h7)
  have t6 := copy_eval a6 1 (slotPort second)
    (by cases second <;> decide) (by decide) (by cases second <;> decide)
    (by cases second <;> simp [a6, a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h8])
  have t7 := clear_eval a7 1
  have hf : cleared a7 1 = extracted a second head slot := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; cases second <;> fin_cases j <;>
        simp [a7, a6, a5, a4, a3, a2, a1, readRegs]
    · funext j; cases second <;>
        simp only [headPort, slotPort, Bool.false_eq_true, ite_false, ite_true, if_true] at hhead hslot <;>
        fin_cases j <;>
        simp [a7, a6, a5, a4, a3, a2, a1,
          clearStacks, copyStacks, sourcePort, headPort, slotPort, h0, h1, h2, hhead, hslot]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq t7))))))
  rw [hf] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  cases second <;>
    simp [a7, a6, a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, slotPort, h1, hh, hs, hi] <;> ring

theorem extracted_workReady (a : Data) (second : Bool) (head slot : List Bool)
    (h : WorkReady a) : WorkReady (extracted a second head slot) := by
  cases second <;> simpa [WorkReady, extracted, headPort, slotPort] using h

theorem normalize_eval (a : Data) (head slot width : List Bool)
    (before after : List (List Bool)) (hwork : WorkReady a)
    (hsource : a.stacks 0 = head ++ before.flatten ++ (slot ++ after.flatten))
    (hw : a.stacks 3 = width) (hi : (a.stacks 25).length = before.length + 1)
    (hh : head.length = width.length) (hs : slot.length = width.length)
    (hc : (a.stacks 17).length = width.length)
    (hb : ∀ row ∈ before, row.length = width.length) :
    Eval normalize ((before.length + 1) * (14 * width.length + 17) + 49 * width.length + 55)
      a (normalized a before after) := by
  rcases hwork with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  let a1 := copied a 17 1
  let a2 := replaceResult a1 (a.stacks 17 ++ (before.flatten ++ (slot ++ after.flatten)))
  let a3 := copied a2 25 2
  let a4 := replaceResult a3 ((a.stacks 17 :: before).flatten ++
    (a.stacks 17 ++ after.flatten))
  have t0 := copy_eval a 17 1 (by decide) (by decide) (by decide) h8
  have t1 := replace_eval a1 [] head (a.stacks 17)
    (before.flatten ++ (slot ++ after.flatten)) width
    (by simpa [a1, copied, copyStacks, List.append_assoc] using hsource)
    (by simp [a1, copyStacks, h1])
    (by simpa [a1, copied, copyStacks] using hw)
    (by simp [a1, copyStacks, h2]) (by simp) hh hc
    (by simpa [a1, copied, copyStacks] using h4)
    (by simpa [a1, copied, copyStacks] using h5)
    (by simpa [a1, copied, copyStacks] using h6)
    (by simpa [a1, copied, copyStacks] using h7)
  have t2 := copy_eval a2 25 2 (by decide) (by decide) (by decide)
    (by simp [a2, a1, copyStacks, h8])
  have t3 := replace_eval a3 (a.stacks 17 :: before) slot (a.stacks 17) after.flatten width
    (by simp [a3, a2, a1, copyStacks, List.append_assoc])
    (by simp [a3, a2, a1, copyStacks, h1])
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using hw)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using hi)
    (by simpa [hc] using hb) hs hc
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h4)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h5)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h6)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h7)
  have t4 := clear_eval a4 1
  have hf : cleared a4 1 = normalized a before after := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, readRegs]
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, clearStacks, copyStacks, normalizedBits, h1, h2,
        List.append_assoc]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq t4)))
  rw [hf] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  simp [a4, a3, a2, a1, copyStacks, h1, hc, hi]
  ring

theorem normalized_workReady (a : Data) (before after : List (List Bool))
    (h : WorkReady a) : WorkReady (normalized a before after) := by
  simpa [WorkReady, normalized] using h

theorem reset_compared_regs (regs : Fin 8 → Bool) (answer : Bool) :
    readRegs (fun j => if j = 7 then answer else if j.val < 5 then false
      else readRegs regs 0 1 none j) 0 1 none =
      (fun j => if j = 7 then answer else if j.val < 5 then false else regs j) := by
  funext j
  by_cases h0 : j = 0
  · subst j; rfl
  by_cases h1 : j = 1
  · subst j; rfl
  simp [readRegs, h0, h1]

theorem program_runsIn (headU slotU headY slotY index width colors positions : List Bool)
    (beforeU afterU beforeY afterY : List (List Bool)) (regs : Fin 8 → Bool)
    (hiU : index.length = beforeU.length + 1) (hiY : index.length = beforeY.length + 1)
    (hhU : headU.length = width.length) (hsU : slotU.length = width.length)
    (hhY : headY.length = width.length) (hsY : slotY.length = width.length)
    (hbU : ∀ row ∈ beforeU, row.length = width.length)
    (hbY : ∀ row ∈ beforeY, row.length = width.length) :
    RunsIn program
      (cost (array headU slotU beforeU afterU) (array headY slotY beforeY afterY) index width)
      ((inputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions regs).withPC (some program.entry))
      ((outputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions headU slotU headY slotY
        (decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY))
        regs).withPC none) := by
  let a := inputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
    index width colors positions regs
  let a1 := copied a 26 3
  let a2 := extracted a1 false headU slotU
  let a3 := normalized a2 beforeU afterU
  let a4 := copied a3 0 28
  let a5 := cleared a4 0
  let a6 := extracted a5 true headY slotY
  let a7 := normalized a6 beforeY afterY
  let a8 := compared a7 (decide (a7.stacks 0 = a7.stacks 28))
  have t0 := copy_eval a 26 3 (by decide) (by decide) (by decide) (by simp [a, inputState])
  have hw1 : WorkReady a1 := by simp [a1, a, copyStacks, inputState, WorkReady]
  have t1 := extract_eval a1 false headU slotU width beforeU afterU hw1
    (by simp [a1, a, copyStacks, inputState])
    (by simp [a1, a, copyStacks, inputState, headPort])
    (by simp [a1, a, copyStacks, inputState, slotPort])
    (by simp [a1, a, copyStacks, inputState, sourcePort, array])
    (by simp [a1, a, copyStacks, inputState])
    (by simpa [a1, a, copied, copyStacks, inputState] using hiU) hhU hsU hbU
  have hw2 : WorkReady a2 := extracted_workReady _ _ _ _ hw1
  have t2 := normalize_eval a2 headU slotU width beforeU afterU hw2
    (by simp [a2, a1, a, extracted, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a2, a1, a, extracted, copyStacks, inputState, headPort, slotPort])
    (by simpa [a2, a1, a, extracted, copied, copyStacks, inputState, headPort, slotPort] using hiU)
    hhU hsU (by simpa [a2, extracted, headPort, slotPort] using hhU) hbU
  have hw3 : WorkReady a3 := normalized_workReady _ _ _ hw2
  have t3 := copy_eval a3 0 28 (by decide) (by decide) (by decide) hw3.2.2.2.2.2.2
  have t4 := clear_eval a4 0
  have hw5 : WorkReady a5 := by simpa [a5, a4, cleared, copied, clearStacks, copyStacks, WorkReady] using hw3
  have t5 := extract_eval a5 true headY slotY width beforeY afterY hw5
    (by simp [a5, clearStacks])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simpa [a5, a4, a3, a2, a1, a, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort] using hiY) hhY hsY hbY
  have hw6 : WorkReady a6 := extracted_workReady _ _ _ _ hw5
  have t6 := normalize_eval a6 headY slotY width beforeY afterY hw6
    (by simp [a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simpa [a6, a5, a4, a3, a2, a1, a, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort] using hiY)
    hhY hsY
    (by simpa [a6, a5, a4, a3, a2, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, headPort, slotPort] using hhU) hbY
  obtain ⟨ne, hne, te⟩ := equality_eval a7
    (by simp [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
  have t8 := clear_eval a8 3
  have ha7left : a7.stacks 0 = normalizedBits headU beforeY afterY := by
    simp [a7, a6, a5, a4, a3, a2, normalized, extracted,
      clearStacks, copyStacks, headPort, slotPort]
  have ha7right : a7.stacks 28 = normalizedBits headU beforeU afterU := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort]
  have ha7regs : a7.regs = readRegs regs 0 1 none := by
    simp only [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      inputState, readRegs_reset]
  have hanswer :
      decide (normalizedBits headU beforeY afterY = normalizedBits headU beforeU afterU) =
      decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY) :=
    decide_eq_decide.mpr eq_comm
  have hf : cleared a8 3 =
      outputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions headU slotU headY slotY
        (decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY)) regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · change readRegs (fun k => if k = 7 then decide (a7.stacks 0 = a7.stacks 28)
        else if k.val < 5 then false else a7.regs k) 0 1 none = _
      rw [ha7left, ha7right, ha7regs, hanswer]
      exact reset_compared_regs regs _
    · funext j; fin_cases j <;>
        simp [a8, a7, a6, a5, a4, a3, a2, a1, a, normalized,
          extracted, inputState, copyStacks, clearStacks, sourcePort, headPort, slotPort]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (te.seq t8)))))))
  rw [hf] at ht
  refine ⟨_, ?_, compiled_halt_trace ht 23 17⟩
  dsimp [cost]
  simp only [a8, a7, a6, a5, a4, a3, a2, a1, a, normalized,
    extracted, inputState, sourcePort, headPort, slotPort, copyStacks, clearStacks,
    Function.update_self, ↓reduceIte] at hne ⊢
  simp [normalizedBits, array, hhU, hsU, hhY, hsY, List.length_append] at hne ⊢
  rw [← hiU, ← hiY]
  nlinarith only [hne]

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extractor on canonical one-hot type encodings. -/

namespace SubexponentialSAT.Subexp.MatrixInputTypes

open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram

variable {r Q Δ : ℕ}

theorem before_length (i : Fin Δ) (u : UniversalType r Q Δ) :
    (before i u).length = i.val := by
  simp [before, slotRows ]

theorem before_width (i : Fin Δ) (u : UniversalType r Q Δ) :
    ∀ row ∈ before i u, row.length = Q * r := by
  intro row hrow
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hrow)
  simp [wordWidth]

theorem slotRows_split (i : Fin Δ) (u : UniversalType r Q Δ) :
    slotRows u = before i u ++ encodeWord (u.slot i) :: after i u := by
  have hi : i.val < (slotRows u).length := by simp [slotRows]
  have h := List.take_append_drop i.val (slotRows u)
  rw [List.drop_eq_getElem_cons hi] at h
  simpa [before, after, slotRows] using h.symm

theorem encodeType_head_slots (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType u = encodeWord u.head ++ (slotRows u).flatten := by
  rw [encodeType_eq_words, List.ofFn_succ]
  simp [slotRows]

theorem encoded_array (i : Fin Δ) (u : UniversalType r Q Δ) :
    array (encodeWord u.head) (encodeWord (u.slot i)) (before i u) (after i u) =
      CollisionProgram.encodeType u := by
  rw [encodeType_head_slots, slotRows_split i u]
  simp [array, List.append_assoc]

theorem slotRows_normalizedType (common : Word r Q) (i : Fin Δ)
    (u : UniversalType r Q Δ) :
    slotRows (normalizedType common i u) = (slotRows u).set i.val (encodeWord common) := by
  apply List.ext_getElem
  · simp [slotRows]
  · intro j hj hk
    simp only [slotRows, List.getElem_ofFn, List.getElem_set]
    by_cases hij : i.val = j
    · have he : (⟨j, by simpa [slotRows] using hj⟩ : Fin Δ) = i := Fin.ext hij.symm
      simp [normalizedType, hij, he]
    · have he : (⟨j, by simpa [slotRows] using hj⟩ : Fin Δ) ≠ i := by
        intro he; exact hij (congrArg Fin.val he).symm
      simp [normalizedType, hij, he]

theorem normalizedType_encoding (common : Word r Q) (i : Fin Δ)
    (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType (normalizedType common i u) =
      normalizedBits (encodeWord common) (before i u) (after i u) := by
  rw [encodeType_head_slots, slotRows_normalizedType, List.set_eq_take_append_cons_drop]
  have hi : i.val < (slotRows u).length := by simp [slotRows]
  simp [hi, normalizedType, normalizedBits, before, after, List.append_assoc]

theorem normalizedType_eq_iff (common : Word r Q) (i : Fin Δ)
    (u y : UniversalType r Q Δ) :
    normalizedType common i u = normalizedType common i y ↔
      ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l := by
  constructor
  · intro h j hj l
    have hs := congrArg (fun z : UniversalType r Q Δ => z.slot j l) h
    simpa [normalizedType, hj] using hs
  · intro h
    apply UniversalType.ext
    · rfl
    · funext j l
      by_cases hj : j = i
      · subst j; simp [normalizedType]
      · simpa [normalizedType, hj] using h j hj l

theorem normalizedBits_eq_iff (common : Word r Q) (i : Fin Δ)
    (u y : UniversalType r Q Δ) :
    normalizedBits (encodeWord common) (before i u) (after i u) =
      normalizedBits (encodeWord common) (before i y) (after i y) ↔
      ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l := by
  rw [← normalizedType_encoding, ← normalizedType_encoding,
    CollisionProgram.encodeType_eq_iff, normalizedType_eq_iff]

/-- Actual type bytes are read and normalized by the fixed extractor; the
spectator bit is produced by the actual equality machine. -/
theorem program_runsIn_oai (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    RunsIn MatrixInputProgram.program
      (36 * CollisionProgram.typeWidth r Q Δ +
        4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265)
      ((input i u y regs).withPC (some MatrixInputProgram.program.entry))
      ((output i u y regs).withPC none) := by
  have h := MatrixInputProgram.program_runsIn
    (encodeWord u.head) (encodeWord (u.slot i))
    (encodeWord y.head) (encodeWord (y.slot i))
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true)
    (before i u) (after i u) (before i y) (after i y) regs
    (by simp [before_length]) (by simp [before_length])
    (by simp [wordWidth]) (by simp [wordWidth])
    (by simp [wordWidth]) (by simp [wordWidth])
    (by simpa using before_width i u) (by simpa using before_width i y)
  have hcost : cost (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
      (List.replicate (i.val + 1) true) (List.replicate (Q * r) true) =
      36 * CollisionProgram.typeWidth r Q Δ +
        4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265 := by
    simp only [cost, CollisionProgram.encodeType_length, List.length_replicate]
    ring
  simpa only [encoded_array, normalizedBits_eq_iff, hcost, input, output] using h

end SubexponentialSAT.Subexp.MatrixInputTypes

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn_oai
