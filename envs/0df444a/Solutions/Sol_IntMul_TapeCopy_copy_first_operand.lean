-- Prove2me | solution 1 for IntMul.TapeCopy.copy_first_operand
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T18:06:36.071015+00:00
-- url     : https://prove2.me/submissions/69d83c43-de72-4472-86ad-45f6ea010014

import Definitions.Def_IntMul_TapeCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace IntMul.TapeCopy

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

/-- Writing immediately after a finite tape word appends one symbol and leaves
all other cells, including the start marker, unchanged. -/
theorem tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf, List.getD_append_right]
      · have hne : p + 1 ≠ w.length + 1 := by omega
        rw [Function.update_of_ne hne]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

/-- The fixed copy machine halts with the first operand as its exact output in
`|x|+2` actual transition steps, for arbitrary second operand and zero-length input. -/
theorem copy_first_operand (x y : List Bool) :
    machine.HaltsWithOutput x y (x.length + 2) x := by
  let c : ℕ → machine.Cfg := fun j =>
    { state := State.copy
      cells := fun i =>
        if i = 0 then machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
        else machine.tapeOf ((x.take j).map machine.bitSym)
      head := fun _ => j + 1 }
  have hstart : machine.step (machine.initCfg x y) = c 0 := by
    apply cfg_ext
    · rfl
    · funext i
      fin_cases i
      · change Function.update (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
          0 Sym.start = machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
        exact Function.update_eq_self 0 _
      · change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
        exact Function.update_eq_self 0 _
    · rfl
  have hstep : ∀ j, j < x.length → machine.step (c j) = c (j + 1) := by
    intro j hj
    have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
    have hinput : (c j).cells 0 ((c j).head 0) = machine.bitSym x[j] := by
      change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD j machine.blank = _
      rw [List.getD_append _ _ _ _ (by simpa using hj)]
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
    have hout : (c j).cells 1 ((c j).head 1) = machine.blank := by
      change ((x.take j).map machine.bitSym).getD j machine.blank = _
      exact List.getD_eq_default _ _ hl.le
    have hb : machine.bitSym x[j] = Sym.zero ∨ machine.bitSym x[j] = Sym.one := by
      cases h : x[j] <;> simp [MultitapeTM.bitSym, h]
    have ht : transition (c j).state (fun i => (c j).cells i ((c j).head i)) =
        (State.copy, fun _ => (machine.bitSym x[j], Move.right)) := by
      change transition State.copy (fun i => (c j).cells i ((c j).head i)) = _
      simp only [transition, hinput, hb, if_true]
      congr 1
      funext i
      fin_cases i <;> simp [hinput, hout]
    apply cfg_ext
    · simp only [MultitapeTM.step, ht]
      rfl
    · simp only [MultitapeTM.step, ht]
      funext i
      fin_cases i
      · change Function.update ((c j).cells 0) ((c j).head 0) (machine.bitSym x[j]) = (c j).cells 0
        rw [← hinput]
        exact Function.update_eq_self _ _
      · change Function.update (machine.tapeOf ((x.take j).map machine.bitSym)) (j + 1)
          (machine.bitSym x[j]) = machine.tapeOf ((x.take (j + 1)).map machine.bitSym)
        have hnew : (x.take (j + 1)).map machine.bitSym =
            (x.take j).map machine.bitSym ++ [machine.bitSym x[j]] := by
          rw [List.take_succ_eq_append_getElem hj, List.map_append]
          rfl
        rw [hnew]
        have hwrite := tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
        rw [hl] at hwrite
        exact hwrite
    · simp only [MultitapeTM.step, ht]
      rfl
  have hrun : ∀ j, j ≤ x.length → machine.step^[j + 1] (machine.initCfg x y) = c j := by
    intro j
    induction j with
    | zero => intro _; simpa using hstart
    | succ j ih =>
        intro hj
        rw [Function.iterate_succ_apply', ih (by omega), hstep j (by omega)]
  have hsep : (c x.length).cells 0 ((c x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hstop : transition (c x.length).state
      (fun i => (c x.length).cells i ((c x.length).head i)) =
      (State.halt, fun i => ((c x.length).cells i ((c x.length).head i), Move.stay)) := by
    change transition State.copy (fun i => (c x.length).cells i ((c x.length).head i)) =
      (State.halt, fun i => ((c x.length).cells i ((c x.length).head i), Move.stay))
    simp only [transition, hsep]
    rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  unfold MultitapeTM.HaltsWithOutput
  rw [show x.length + 2 = (x.length + 1) + 1 by omega,
    Function.iterate_succ_apply', hrun _ le_rfl]
  constructor
  · simp only [MultitapeTM.step, hstop]
  · simp only [MultitapeTM.step, hstop]
    change Function.update ((c x.length).cells machine.outTape) ((c x.length).head machine.outTape)
      ((c x.length).cells machine.outTape ((c x.length).head machine.outTape)) = machine.tapeOf (x.map machine.bitSym)
    rw [Function.update_eq_self]
    change machine.tapeOf ((x.take x.length).map machine.bitSym) = _
    rw [List.take_length]

end IntMul.TapeCopy

#print axioms IntMul.TapeCopy.copy_first_operand


theorem solution (x y : List Bool) :
    IntMul.TapeCopy.machine.HaltsWithOutput x y (x.length + 2) x := by
  exact IntMul.TapeCopy.copy_first_operand x y

#print axioms solution
