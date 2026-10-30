-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:08:52.149882+00:00
-- url     : https://prove2.me/submissions/c20cb973-3f23-4aab-a962-035c5972f45c

import Mathlib
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines

theorem low_injective : Function.Injective low := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 42 => k.val) h)

theorem read_eval (a : Data) (before : List (List Bool)) (row rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval read (before.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (readResult a row) := by
  let b : State 10 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.readStacks row (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 10) 1 (by decide)
    before row rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hw rfl hi hb hr h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 10) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hin : embedState id low a ⟨a.regs, a.stacks ∘ low⟩ = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective <;> intros <;> rfl
  have hout : embedState id low a b = readResult a row := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [readResult, b, low, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [readResult, h1, h2]
  simpa only [hin, hout, read] using he

theorem copy_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst)
    (hs8 : src ≠ 8) (h8d : (8 : Fin 42) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 8 (0 : Fin 10) 1 hsd hs8 h8d (by decide) a h8

theorem transfer_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred a src dst) :=
  TupleProgram.transfer_eval src dst (0 : Fin 10) 1 hsd (by decide) a

theorem move_eval (a : Data) (src dst : Fin 42) (hs8 : src ≠ 8)
    (h8d : (8 : Fin 42) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (move src dst) (6 * (a.stacks src).length + 6) a (moved a src dst) := by
  have he := (transfer_eval a src 8 hs8).seq (transfer_eval (transferred a src 8) 8 dst h8d)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [moved, transferred, transferStacks, h8] <;> omega

theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 10) 1 a

theorem readOne_eval (a : Data) (i : Fin 4) (before : List (List Bool)) (row rest : List Bool)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : a.stacks (target i) = [])
    (hs : a.stacks (source i) = before.flatten ++ (row ++ rest))
    (hi : (a.stacks 37).length = before.length)
    (hb : ∀ x ∈ before, x.length = (a.stacks 21).length)
    (hr : row.length = (a.stacks 21).length) :
    Eval (readOne i)
      (9 * (a.stacks (source i)).length + before.length * (14 * (a.stacks 21).length + 17) +
        30 * (a.stacks 21).length + 43) a (readOneResult a i row) := by
  have hw0 := hwork 0 (by decide)
  have hw1 := hwork 1 (by decide)
  have hw2 := hwork 2 (by decide)
  have hw3 := hwork 3 (by decide)
  have hw4 := hwork 4 (by decide)
  have hw5 := hwork 5 (by decide)
  have hw6 := hwork 6 (by decide)
  have hw7 := hwork 7 (by decide)
  have hw8 := hwork 8 (by decide)
  let a1 := copied a (source i) 0
  let a2 := copied a1 21 3
  let a3 := copied a2 37 2
  let a4 := readResult a3 row
  let a5 := moved a4 1 (target i)
  let a6 := cleared a5 0
  let a7 := cleared a6 3
  have t0 := copy_eval a (source i) 0
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by decide) (hwork 8 (by decide))
  have t1 := copy_eval a1 21 3 (by decide) (by decide) (by decide)
    (by fin_cases i <;> simp +decide [a1, copied, copyStacks, source, hw8])
  have t2 := copy_eval a2 37 2 (by decide) (by decide) (by decide)
    (by fin_cases i <;> simp +decide [a2, a1, copied, copyStacks, source, hw8])
  have t3 := read_eval a3 before row rest (a.stacks 21)
    (by fin_cases i <;> simpa +decide [a3, a2, a1, copied, copyStacks, source, hw0] using hs)
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw3])
    (by fin_cases i <;> simpa +decide [a3, a2, a1, copied, copyStacks, source, hw2] using hi)
    hb hr
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw4])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw5])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw6])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw7])
  have t4 := move_eval a4 1 (target i) (by decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> simp +decide [a4, a3, a2, a1, readResult, copied, copyStacks, source, hw8])
  have t5 := clear_eval a5 0
  have t6 := clear_eval a6 3
  have hf : a7 = readOneResult a i row := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;>
        simp [ a6, a5, a4, a3, a2, a1, cleared, moved,
          transferred, readResult, copied, readRegs]
    · funext j
      fin_cases i <;> fin_cases j <;>
        simp +decide [ a6, a5, a4, a3, a2, a1, cleared, moved,
          transferred, readResult, copied, clearStacks, transferStacks, copyStacks,
          source, target, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8] at hd ⊢
      all_goals first | exact hd
  change cleared a6 3 = readOneResult a i row at hf
  have he := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq t6)))))
  rw [hf] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  fin_cases i <;>
    simp +decide [a6, a5, a4, a3, a2, a1, readResult, cleared, moved, transferred,
      copied, clearStacks, transferStacks, copyStacks, source, target,
      hw0, hw1, hw2, hw3, hw8, hr, hi]
    <;> ring

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

theorem wordRows_split (w : Word r Q) (t : Fin Q) :
    wordRows w = (wordRows w).take t.val ++ colorWord (w t) :: (wordRows w).drop (t.val + 1) := by
  have ht : t.val < (wordRows w).length := by simp [wordRows]
  have h := List.take_append_drop t.val (wordRows w)
  rw [List.drop_eq_getElem_cons ht] at h
  simpa [wordRows] using h.symm

theorem encodeWord_split (w : Word r Q) (t : Fin Q) :
    ReadPlan.encodeWord w = ((wordRows w).take t.val).flatten ++
      (colorWord (w t) ++ ((wordRows w).drop (t.val + 1)).flatten) := by
  change (wordRows w).flatten = _
  conv_lhs => rw [wordRows_split w t]
  simp

theorem readOne_typed (a : Data) (i : Fin 4) (w : Word r Q) (t : Fin Q)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : a.stacks (target i) = []) (hs : a.stacks (source i) = ReadPlan.encodeWord w)
    (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
    Eval (readOne i) (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)
      a (readOneResult a i (colorWord (w t))) := by
  have h := readOne_eval a i ((wordRows w).take t.val) (colorWord (w t))
    (((wordRows w).drop (t.val + 1)).flatten) hwork hd
    (by rw [hs, encodeWord_split])
    (by simpa [wordRows, Nat.min_eq_left t.isLt.le] using hi)
    (by
      intro row hrow
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hrow)
      simp [hw])
    (by simp [hw])
  simpa [hs, hw, wordRows, Nat.min_eq_left t.isLt.le, ReadPlan.wordWidth] using h

theorem readOneResult_work (a : Data) (i : Fin 4) (word : List Bool)
    (h : ∀ j : Fin 42, j.val < 9 → a.stacks j = []) :
    ∀ j : Fin 42, j.val < 9 → (readOneResult a i word).stacks j = [] := by
  intro j hj
  have hn : j ≠ target i := by
    intro he
    have hv := congrArg (fun k : Fin 42 => k.val) he
    change j.val = 38 + i.val at hv
    omega
  simpa [readOneResult, hn] using h j hj

theorem readFour_typed_oai (a : Data) (words : Fin 4 → Word r Q) (t : Fin Q)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : ∀ i, a.stacks (target i) = [])
    (hs : ∀ i, a.stacks (source i) = ReadPlan.encodeWord (words i))
    (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
    Eval readFour (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)) a
      (fourReadResult a (fun i => colorWord (words i t))) := by
  let a1 := readOneResult a 0 (colorWord (words 0 t))
  let a2 := readOneResult a1 1 (colorWord (words 1 t))
  let a3 := readOneResult a2 2 (colorWord (words 2 t))
  have h1 := readOne_typed a 0 (words 0) t hwork (hd 0) (hs 0) hi hw
  have w1 := readOneResult_work a 0 (colorWord (words 0 t)) hwork
  have h2 := readOne_typed a1 1 (words 1) t w1
    (by simpa [a1, readOneResult, target] using hd 1)
    (by simpa [a1, readOneResult, source, target] using hs 1)
    (by simpa [a1, readOneResult, target] using hi)
    (by simpa [a1, readOneResult, target] using hw)
  have w2 := readOneResult_work a1 1 (colorWord (words 1 t)) w1
  have h3 := readOne_typed a2 2 (words 2) t w2
    (by simpa [a2, a1, readOneResult, target] using hd 2)
    (by simpa [a2, a1, readOneResult, source, target] using hs 2)
    (by simpa [a2, a1, readOneResult, target] using hi)
    (by simpa [a2, a1, readOneResult, target] using hw)
  have w3 := readOneResult_work a2 2 (colorWord (words 2 t)) w2
  have h4 := readOne_typed a3 3 (words 3) t w3
    (by simpa [a3, a2, a1, readOneResult, target] using hd 3)
    (by simpa [a3, a2, a1, readOneResult, source, target] using hs 3)
    (by simpa [a3, a2, a1, readOneResult, target] using hi)
    (by simpa [a3, a2, a1, readOneResult, target] using hw)
  have he := h1.seq (h2.seq (h3.seq h4))
  convert he using 1
  · ring
  · simp [fourReadResult, a3, a2, a1]

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed_oai
