-- Prove2me | solution 1 for IntMul.CountedStream.template_reset_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T19:17:39.183958+00:00
-- url     : https://prove2.me/submissions/b12cb749-3282-42bf-91b3-74c94f2d026d

import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem reset_left_transition (a : Fin 4 → Sym) (x y : Bool)
    (hx : a 2 = machine.bitSym x) (hy : a 3 = machine.bitSym y) :
    transition .resetLeft a = (.resetLeft, fun i =>
      (if i = 2 then a 3 else a i, if i = 2 ∨ i = 3 then .left else .stay)) := by
  have hb : a 2 = Sym.zero ∨ a 2 = Sym.one := by rw [hx]; cases x <;> decide
  simp only [transition, rawTransition, if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · change safeStep (a 2) (a 3) .left = (a 3, .left)
    rw [hx, hy]
    cases x <;> cases y <;> decide
  · change safeStep (a 3) (a 3) .left = (a 3, .left)
    rw [hy]
    exact safe_left _ (bit_ne_start y)

private theorem reset_left_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) : transition .resetLeft a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem reset_right_bit_transition (a : Fin 4 → Sym)
    (hx : a 2 = .zero ∨ a 2 = .one) : transition .resetRight a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos hx]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem reset_right_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) (hy : a 3 = .sep) : transition .resetRight a =
      (.halt, fun i => (a i, if i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi]
    apply safe_left
    rcases hi with rfl | rfl
    · rw [hx]; decide
    · rw [hy]; decide
  · simp only [if_neg hi, safe_stay]
/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem tape_replace_after_prefix (M : MultitapeTM)
    (pre post : List M.Sym) (old new : M.Sym) :
    Function.update (M.tapeOf (pre ++ old :: post)) (pre.length + 1) new =
      M.tapeOf (pre ++ new :: post) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases he : p = pre.length
      · subst p
        simp [MultitapeTM.tapeOf, List.getD_append_right]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ pre.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hl : p < pre.length
        · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
        · have hge : pre.length ≤ p := by omega
          rw [List.getD_append_right _ _ _ _ hge, List.getD_append_right _ _ _ _ hge]
          cases hd : p - pre.length with
          | zero => omega
          | succ d => simp



private theorem reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem reset_left_read (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
    (h : xs.length = ys.length) :
    (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells 2 (xs.length + 2) = machine.bitSym a ∧
    (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells 3 (xs.length + 2) = machine.bitSym b := by
  constructor
  · change (machine.tapeOf (Sym.sep :: (((a :: xs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
      (xs.length + 2) = _
    rw [show xs.length + 2 = (xs.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    exact reverse_last a xs done
  · change (machine.tapeOf (Sym.sep :: (((b :: ys).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
      (xs.length + 2) = _
    rw [h, show ys.length + 2 = (ys.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    exact reverse_last b ys done

private theorem reset_left_step (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
    (h : xs.length = ys.length) :
    machine.step (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)) =
        resetFrame base .resetLeft (xs.reverse ++ b :: done) (ys.reverse ++ b :: done) (xs.length + 1) := by
  let f := resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done) (xs.length + 2)
  have hx : f.cells 2 (f.head 2) = machine.bitSym a := (reset_left_read base a b xs ys done h).1
  have hy : f.cells 3 (f.head 3) = machine.bitSym b := (reset_left_read base a b xs ys done h).2
  have ht := reset_left_transition (fun i => f.cells i (f.head i)) a b hx hy
  change transition (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).state
    (fun i => (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells i ((resetFrame base .resetLeft ((a :: xs).reverse ++ done)
        ((b :: ys).reverse ++ done) (xs.length + 2)).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht, hy]
    funext i
    fin_cases i
    · change Function.update (f.cells 0) (f.head 0) (f.cells 0 (f.head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (f.cells 1) (f.head 1) (f.cells 1 (f.head 1)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update
        (machine.tapeOf (Sym.sep :: (((a :: xs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (xs.length + 2) (machine.bitSym b) =
          machine.tapeOf (Sym.sep :: ((xs.reverse ++ b :: done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse, List.map_nil, List.nil_append] using
        tape_replace_after_prefix machine (Sym.sep :: xs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) (machine.bitSym a) (machine.bitSym b)
    · change Function.update (f.cells 3) (f.head 3) (f.cells 3 (f.head 3)) = _
      rw [Function.update_eq_self]
      simp [f, resetFrame, List.reverse_cons, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [resetFrame]

private theorem reset_left_run (base : machine.Cfg) (xs ys done : List Bool) (h : xs.length = ys.length) :
    machine.step^[xs.length]
      (resetFrame base .resetLeft (xs.reverse ++ done) (ys.reverse ++ done) (xs.length + 1)) =
        resetFrame base .resetLeft (ys.reverse ++ done) (ys.reverse ++ done) 1 := by
  induction xs generalizing ys done with
  | nil =>
      cases ys with
      | nil => simp
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [List.length_cons, Function.iterate_succ_apply]
          change machine.step^[xs.length]
            (machine.step (resetFrame base .resetLeft ((a :: xs).reverse ++ done)
              ((b :: ys).reverse ++ done) (xs.length + 2))) = _
          rw [reset_left_step base a b xs ys done ht, ih ys (b :: done) ht]
          simp [List.reverse_cons, List.append_assoc]


private theorem reset_left_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetLeft word word 1) = resetFrame base .resetRight word word 2 := by
  have hs : (resetFrame base .resetLeft word word 1).cells 2
      ((resetFrame base .resetLeft word word 1).head 2) = Sym.sep := rfl
  have ht := reset_left_sep_transition
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) hs
  change transition (resetFrame base .resetLeft word word 1).state
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetLeft word word 1).cells i)
      ((resetFrame base .resetLeft word word 1).head i)
      ((resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi]

private theorem reset_right_step (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j < word.length) :
    machine.step (resetFrame base .resetRight word word (j + 2)) =
      resetFrame base .resetRight word word ((j + 1) + 2) := by
  have hr : (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = machine.bitSym word[j] := by
    change (machine.tapeOf (Sym.sep :: (word.map machine.bitSym ++ [Sym.sep]))) (j + 2) = _
    rw [show j + 2 = (j + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = Sym.zero ∨
      (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = Sym.one := by
    rw [hr]
    cases word[j] <;> decide
  have ht := reset_right_bit_transition
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) hb
  change transition (resetFrame base .resetRight word word (j + 2)).state
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetRight word word (j + 2)).cells i)
      ((resetFrame base .resetRight word word (j + 2)).head i)
      ((resetFrame base .resetRight word word (j + 2)).cells i
        ((resetFrame base .resetRight word word (j + 2)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi] <;> omega

private theorem reset_right_run (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j ≤ word.length) :
    machine.step^[j] (resetFrame base .resetRight word word 2) = resetFrame base .resetRight word word (j + 2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), reset_right_step base word j (by omega)]

private theorem reset_right_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetRight word word (word.length + 2)) =
      resetFrame base .halt word word (word.length + 1) := by
  have hs : (resetFrame base .resetRight word word (word.length + 2)).cells 2
      ((resetFrame base .resetRight word word (word.length + 2)).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: (word.map machine.bitSym ++ [Sym.sep]))) (word.length + 2) = _
    rw [show word.length + 2 = (word.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := reset_right_sep_transition
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) hs hs
  change transition (resetFrame base .resetRight word word (word.length + 2)).state
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetRight word word (word.length + 2)).cells i)
      ((resetFrame base .resetRight word word (word.length + 2)).head i)
      ((resetFrame base .resetRight word word (word.length + 2)).cells i
        ((resetFrame base .resetRight word word (word.length + 2)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi]

/-- Literal saved-template reset, including restoration of BOTH work heads.
The arbitrary input/output tapes and their heads remain exactly unchanged. -/
theorem template_reset_correct (base : machine.Cfg) (bits template : List Bool)
    (h : bits.length = template.length) :
    machine.step^[2 * bits.length + 2]
      (resetFrame base .resetLeft bits template (bits.length + 1)) =
        resetFrame base .halt template template (template.length + 1) := by
  have hf : resetFrame base .resetLeft bits template (bits.length + 1) =
      resetFrame base .resetLeft (bits.reverse.reverse ++ []) (template.reverse.reverse ++ [])
        (bits.reverse.length + 1) := by simp
  rw [hf]
  have hl : machine.step^[bits.length + 1]
      (resetFrame base .resetLeft (bits.reverse.reverse ++ []) (template.reverse.reverse ++ [])
        (bits.reverse.length + 1)) = resetFrame base .resetRight template template 2 := by
    rw [Function.iterate_succ_apply']
    have he := reset_left_run base bits.reverse template.reverse [] (by simpa using h)
    simp only [List.length_reverse] at he ⊢
    rw [he]
    simp only [List.reverse_reverse, List.append_nil]
    exact reset_left_end base template
  rw [show 2 * bits.length + 2 = (template.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply, hl, Function.iterate_succ_apply',
    reset_right_run base template template.length le_rfl, reset_right_end]

end IntMul.CountedStream


theorem solution (base : IntMul.CountedStream.machine.Cfg) (bits template : List Bool)
    (h : bits.length = template.length) :
    IntMul.CountedStream.machine.step^[2 * bits.length + 2]
      (IntMul.CountedStream.resetFrame base .resetLeft bits template (bits.length + 1)) =
        IntMul.CountedStream.resetFrame base .halt template template (template.length + 1) :=
  IntMul.CountedStream.template_reset_correct base bits template h

#print axioms solution
