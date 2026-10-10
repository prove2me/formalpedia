-- Prove2me | solution 2 for IntMul.TM.schoolbook
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T20:39:19.189332+00:00
-- url     : https://prove2.me/submissions/296c1401-cc75-4204-aec0-0ddde9925354

import Definitions.Def_IntMul_TapeSchoolbook
import Theorems.Thm_IntMul_BinarySchoolbook_product_word_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace IntMul.BinarySchoolbook

private theorem shift_length (previous : Bool) (p : List Bool) :
    (shiftCarry previous p).length = p.length := by
  induction p generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [shiftCarry,ih]

private theorem add_fixed_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addFixed x y c).length = x.length := by
  induction x generalizing y c with
  | nil => simp [addFixed]
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp [addFixed,ih ys _ ht]

private theorem advance_length (x p : List Bool) (b : Bool) (h : x.length = p.length) :
    (advanceWord x p b).length = x.length := by
  cases b
  · simp [advanceWord,shift_length,h]
  · simp only [advanceWord,↓reduceIte]
    rw [add_fixed_length _ _ _ (by simpa [shift_length] using h.symm),shift_length,h]

end IntMul.BinarySchoolbook


namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)
open IntMul.BinarySchoolbook (shiftCarry highCarry)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem shift_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem shift_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem shift_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem shift_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem shift_shift_length (previous : Bool) (bits : List Bool) :
    (shiftCarry previous bits).length = bits.length := by
  induction bits generalizing previous with
  | nil => rfl
  | cons b bs ih => simp [shiftCarry,ih]

private theorem shift_bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem shift_shift_bit_transition (a : Fin 4 → Sym) (add previous b : Bool)
    (h : a 1 = machine.bitSym b) :
    transition (.shift add previous) a =
      (.shift add b,fun i => (if i = 1 then machine.bitSym previous else a i,
        if i = 1 then .left else .stay)) := by
  simp only [transition,rawTransition,h,if_neg (shift_bit_ne_start b)]
  congr 1
  · cases b <;> rfl
  · funext i
    by_cases hi : i = 1
    · subst i
      simp only [if_pos rfl]
      rw [h]
      cases b <;> cases previous <;> decide
    · simp only [if_neg hi,safe_stay]

private theorem shift_shift_read (base : machine.Cfg) (add previous b : Bool) (bs done : List Bool) :
    (shiftFrame base add previous (b :: bs) done).cells 1
      ((shiftFrame base add previous (b :: bs) done).head 1) = machine.bitSym b := by
  change (machine.tapeOf (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
    (bs.length + 1) = _
  simp only [MultitapeTM.tapeOf,List.reverse_cons,List.map_append,List.map_cons,
    List.map_nil,List.append_assoc,List.singleton_append]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem shift_shift_bit_step (base : machine.Cfg) (add previous b : Bool) (bs done : List Bool) :
    machine.step (shiftFrame base add previous (b :: bs) done) =
      shiftFrame base add b bs (previous :: done) := by
  have ht := shift_shift_bit_transition
    (fun i => (shiftFrame base add previous (b :: bs) done).cells i
      ((shiftFrame base add previous (b :: bs) done).head i)) add previous b
    (shift_shift_read base add previous b bs done)
  change transition (shiftFrame base add previous (b :: bs) done).state
    (fun i => (shiftFrame base add previous (b :: bs) done).cells i
      ((shiftFrame base add previous (b :: bs) done).head i)) = _ at ht
  apply shift_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1
    · subst i
      change Function.update (machine.tapeOf (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
        (bs.length + 1) (machine.bitSym previous) =
          machine.tapeOf ((bs.reverse ++ previous :: done).map machine.bitSym ++ [Sym.sep])
      simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_singleton,
        List.map_nil,List.nil_append,List.append_assoc,List.singleton_append,List.cons_append,List.length_map,List.length_reverse] using
        shift_tape_replace_after_prefix machine (bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) (machine.bitSym b) (machine.bitSym previous)
    · simp only [if_neg hi]
      change Function.update ((shiftFrame base add previous (b :: bs) done).cells i)
        ((shiftFrame base add previous (b :: bs) done).head i)
        ((shiftFrame base add previous (b :: bs) done).cells i
          ((shiftFrame base add previous (b :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [shiftFrame,hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1 <;> simp [shiftFrame,hi]

private theorem shift_shift_run (base : machine.Cfg) (add previous : Bool) (bits done : List Bool) :
    machine.step^[bits.length] (shiftFrame base add previous bits done) =
      shiftFrame base add (highCarry previous bits) [] ((shiftCarry previous bits).reverse ++ done) := by
  induction bits generalizing previous done with
  | nil => simp [highCarry,shiftCarry]
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,shift_shift_bit_step,ih]
      simp [highCarry,shiftCarry,List.reverse_cons,List.append_assoc]

private theorem shift_shift_marker_transition (a : Fin 4 → Sym) (add previous : Bool)
    (h : a 1 = .start) : transition (.shift add previous) a =
      (.rewindShift add,fun i => (a i,if i = 1 then .right else .stay)) := by
  simp only [transition,rawTransition,h,if_true]
  congr 1
  funext i
  by_cases hi : i = 1
  · simp only [if_pos hi,shift_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem shift_shift_nil_step (base : machine.Cfg) (add previous : Bool) (done : List Bool) :
    machine.step (shiftFrame base add previous [] done) = returnShiftFrame base add [] done := by
  have ht := shift_shift_marker_transition
    (fun i => (shiftFrame base add previous [] done).cells i
      ((shiftFrame base add previous [] done).head i)) add previous rfl
  change transition (shiftFrame base add previous [] done).state
    (fun i => (shiftFrame base add previous [] done).cells i
      ((shiftFrame base add previous [] done).head i)) = _ at ht
  apply shift_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [shiftFrame,returnShiftFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1 <;> simp [shiftFrame,returnShiftFrame,hi]

private theorem shift_return_bit_transition (a : Fin 4 → Sym) (add : Bool)
    (h : a 1 = .zero ∨ a 1 = .one) :
    transition (.rewindShift add) a =
      (.rewindShift add,fun i => (a i,if i = 1 then .right else .stay)) := by
  simp only [transition,rawTransition,if_pos h]
  congr 1
  funext i
  by_cases hi : i = 1
  · simp only [if_pos hi,shift_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem shift_return_read (base : machine.Cfg) (add b : Bool) (pre bs : List Bool) :
    (returnShiftFrame base add pre (b :: bs)).cells 1
      ((returnShiftFrame base add pre (b :: bs)).head 1) = machine.bitSym b := by
  change ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep]).getD pre.length machine.blank = _
  simp only [List.map_append,List.map_cons,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem shift_return_bit_step (base : machine.Cfg) (add b : Bool) (pre bs : List Bool) :
    machine.step (returnShiftFrame base add pre (b :: bs)) =
      returnShiftFrame base add (pre ++ [b]) bs := by
  have hr := shift_return_read base add b pre bs
  have hb : (returnShiftFrame base add pre (b :: bs)).cells 1
      ((returnShiftFrame base add pre (b :: bs)).head 1) = Sym.zero ∨
        (returnShiftFrame base add pre (b :: bs)).cells 1
          ((returnShiftFrame base add pre (b :: bs)).head 1) = Sym.one := by
    rw [hr]
    cases b <;> decide
  have ht := shift_return_bit_transition
    (fun i => (returnShiftFrame base add pre (b :: bs)).cells i
      ((returnShiftFrame base add pre (b :: bs)).head i)) add hb
  change transition (returnShiftFrame base add pre (b :: bs)).state
    (fun i => (returnShiftFrame base add pre (b :: bs)).cells i
      ((returnShiftFrame base add pre (b :: bs)).head i)) = _ at ht
  apply shift_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [returnShiftFrame,List.append_assoc]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1 <;> simp [returnShiftFrame,hi]

private theorem shift_return_sep_transition (a : Fin 4 → Sym) (add : Bool) (h : a 1 = .sep) :
    transition (.rewindShift add) a =
      (if add then .add false else .advance,fun i => (a i,if i = 1 then .left else .stay)) := by
  simp only [transition,rawTransition,h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  by_cases hi : i = 1
  · subst i
    simp only [if_pos rfl]
    rw [h]
    exact shift_safe_left _ (by decide)
  · simp only [if_neg hi,safe_stay]

private theorem shift_return_nil_step (base : machine.Cfg) (add : Bool) (pre : List Bool) :
    machine.step (returnShiftFrame base add pre []) =
      productFrame base (if add then .add false else .advance) pre pre.length := by
  have hr : (returnShiftFrame base add pre []).cells 1
      ((returnShiftFrame base add pre []).head 1) = Sym.sep := by
    change ((pre ++ []).map machine.bitSym ++ [Sym.sep]).getD pre.length machine.blank = _
    simp only [List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := shift_return_sep_transition
    (fun i => (returnShiftFrame base add pre []).cells i
      ((returnShiftFrame base add pre []).head i)) add hr
  change transition (returnShiftFrame base add pre []).state
    (fun i => (returnShiftFrame base add pre []).cells i
      ((returnShiftFrame base add pre []).head i)) = _ at ht
  apply shift_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [returnShiftFrame,productFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1 <;> simp [returnShiftFrame,productFrame,hi]

private theorem shift_return_run (base : machine.Cfg) (add : Bool) (pre right : List Bool) :
    machine.step^[right.length + 1] (returnShiftFrame base add pre right) =
      productFrame base (if add then .add false else .advance) (pre ++ right) (pre.length + right.length) := by
  induction right generalizing pre with
  | nil => simpa using shift_return_nil_step base add pre
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply,shift_return_bit_step,ih]
      simp [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The physical fixed-width shift and complete return of the product head.
Every other tape and head is preserved from the arbitrary base configuration. -/
private theorem shift_correct (base : machine.Cfg) (add previous : Bool) (bits done : List Bool) :
    machine.step^[2 * bits.length + done.length + 2] (shiftFrame base add previous bits done) =
      productFrame base (if add then .add false else .advance)
        ((shiftCarry previous bits).reverse ++ done) (bits.length + done.length) := by
  let word := (shiftCarry previous bits).reverse ++ done
  have hw : word.length = bits.length + done.length := by simp [word,shift_shift_length]
  have ht : 2 * bits.length + done.length + 2 = (word.length + 1 + 1) + bits.length := by omega
  rw [ht,Function.iterate_add_apply,shift_shift_run,Function.iterate_succ_apply,shift_shift_nil_step,shift_return_run]
  simp only [List.nil_append,List.length_nil,Nat.zero_add]
  rw [hw]

end IntMul.TapeSchoolbook



namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)
open IntMul.BinarySchoolbook (addFixed lastCarry)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem add_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem add_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem add_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem add_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem add_add_length (p x : List Bool) (c : Bool) (h : p.length = x.length) :
    (addFixed p x c).length = p.length := by
  induction p generalizing x c with
  | nil => simp [addFixed]
  | cons a ps ih =>
      cases x with
      | nil => simp at h
      | cons b xs => simp [addFixed,ih xs _ (by simpa using h)]

private theorem add_bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem add_add_bit_transition (a : Fin 4 → Sym) (c p x : Bool)
    (hp : a 1 = machine.bitSym p) (hx : a 2 = machine.bitSym x) :
    transition (.add c) a = (.add (BinaryAdder.carryBit p x c),fun i =>
      (if i = 1 then machine.bitSym (BinaryAdder.sumBit p x c) else a i,
        if i = 1 ∨ i = 2 then .left else .stay)) := by
  simp only [transition,rawTransition,hp,if_neg (add_bit_ne_start p)]
  congr 1
  · rw [hx]
    cases p <;> cases x <;> rfl
  · funext i
    fin_cases i
    · exact safe_stay _
    · change safeStep (a 1)
        (TapeAdder.encode (BinaryAdder.sumBit (TapeAdder.decode (machine.bitSym p)) (TapeAdder.decode (a 2)) c)) .left =
          (machine.bitSym (BinaryAdder.sumBit p x c),.left)
      rw [hp,hx]
      cases p <;> cases x <;> cases c <;> decide
    · change safeStep (a 2) (a 2) .left = (a 2,.left)
      rw [hx]
      exact add_safe_left _ (add_bit_ne_start x)
    · exact safe_stay _

private theorem add_reverse_read (b : Bool) (bs done : List Bool) :
    (machine.tapeOf (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
      (bs.length + 1) = machine.bitSym b := by
  simp only [MultitapeTM.tapeOf,List.reverse_cons,List.map_append,List.map_cons,
    List.append_assoc,List.singleton_append]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem add_add_read (base : machine.Cfg) (c a b : Bool) (ps xs dp dx : List Bool) :
    (addFrame base c (a :: ps) (b :: xs) dp dx).cells 1
      ((addFrame base c (a :: ps) (b :: xs) dp dx).head 1) = machine.bitSym a ∧
    (addFrame base c (a :: ps) (b :: xs) dp dx).cells 2
      ((addFrame base c (a :: ps) (b :: xs) dp dx).head 2) = machine.bitSym b := by
  constructor
  · exact add_reverse_read a ps dp
  · exact add_reverse_read b xs dx

private theorem add_add_bit_step (base : machine.Cfg) (c a b : Bool) (ps xs dp dx : List Bool) :
    machine.step (addFrame base c (a :: ps) (b :: xs) dp dx) =
      addFrame base (BinaryAdder.carryBit a b c) ps xs (BinaryAdder.sumBit a b c :: dp) (b :: dx) := by
  have ht := add_add_bit_transition
    (fun i => (addFrame base c (a :: ps) (b :: xs) dp dx).cells i
      ((addFrame base c (a :: ps) (b :: xs) dp dx).head i)) c a b
      (add_add_read base c a b ps xs dp dx).1 (add_add_read base c a b ps xs dp dx).2
  change transition (addFrame base c (a :: ps) (b :: xs) dp dx).state
    (fun i => (addFrame base c (a :: ps) (b :: xs) dp dx).cells i
      ((addFrame base c (a :: ps) (b :: xs) dp dx).head i)) = _ at ht
  apply add_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · change Function.update ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 0)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).head 0)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 0
          ((addFrame base c (a :: ps) (b :: xs) dp dx).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update
        (machine.tapeOf (((a :: ps).reverse ++ dp).map machine.bitSym ++ [Sym.sep]))
        (ps.length + 1) (machine.bitSym (BinaryAdder.sumBit a b c)) =
          machine.tapeOf ((ps.reverse ++ BinaryAdder.sumBit a b c :: dp).map machine.bitSym ++ [Sym.sep])
      simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_singleton,
        List.map_nil,List.nil_append,List.append_assoc,List.singleton_append,List.cons_append,
        List.length_map,List.length_reverse] using
        add_tape_replace_after_prefix machine (ps.reverse.map machine.bitSym)
          (dp.map machine.bitSym ++ [Sym.sep]) (machine.bitSym a) (machine.bitSym (BinaryAdder.sumBit a b c))
    · change Function.update ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 2)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).head 2)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 2
          ((addFrame base c (a :: ps) (b :: xs) dp dx).head 2)) = _
      rw [Function.update_eq_self]
      simp [addFrame,List.reverse_cons,List.append_assoc]
    · change Function.update ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 3)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).head 3)
        ((addFrame base c (a :: ps) (b :: xs) dp dx).cells 3
          ((addFrame base c (a :: ps) (b :: xs) dp dx).head 3)) = _
      rw [Function.update_eq_self]
      rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [addFrame]

private theorem add_add_run (base : machine.Cfg) (c : Bool) (p x dp dx : List Bool)
    (h : p.length = x.length) :
    machine.step^[p.length] (addFrame base c p x dp dx) =
      addFrame base (lastCarry p x c) [] [] ((addFixed p x c).reverse ++ dp) (x.reverse ++ dx) := by
  induction p generalizing x c dp dx with
  | nil =>
      cases x with
      | nil => simp [lastCarry,addFixed]
      | cons b xs => simp at h
  | cons a ps ih =>
      cases x with
      | nil => simp at h
      | cons b xs =>
          have ht : ps.length = xs.length := by simpa using h
          rw [List.length_cons,Function.iterate_succ_apply,add_add_bit_step,ih _ _ _ _ ht]
          simp [lastCarry,addFixed,List.reverse_cons,List.append_assoc]

private theorem add_add_marker_transition (a : Fin 4 → Sym) (c : Bool) (h : a 1 = .start) :
    transition (.add c) a = (.rewindAdd,fun i => (a i,if i = 1 ∨ i = 2 then .right else .stay)) := by
  simp only [transition,rawTransition,h,if_true]
  congr 1
  funext i
  by_cases hi : i = 1 ∨ i = 2
  · simp only [if_pos hi,add_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem add_add_nil_step (base : machine.Cfg) (c : Bool) (dp dx : List Bool) :
    machine.step (addFrame base c [] [] dp dx) = returnAddFrame base [] dp dx := by
  have ht := add_add_marker_transition
    (fun i => (addFrame base c [] [] dp dx).cells i ((addFrame base c [] [] dp dx).head i)) c rfl
  change transition (addFrame base c [] [] dp dx).state
    (fun i => (addFrame base c [] [] dp dx).cells i ((addFrame base c [] [] dp dx).head i)) = _ at ht
  apply add_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [addFrame,returnAddFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [addFrame,returnAddFrame]

private theorem add_return_bit_transition (a : Fin 4 → Sym)
    (h : a 1 = .zero ∨ a 1 = .one) : transition .rewindAdd a =
      (.rewindAdd,fun i => (a i,if i = 1 ∨ i = 2 then .right else .stay)) := by
  simp only [transition,rawTransition,if_pos h]
  congr 1
  funext i
  by_cases hi : i = 1 ∨ i = 2
  · simp only [if_pos hi,add_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem add_return_read (base : machine.Cfg) (b : Bool) (pre bs x : List Bool) :
    (returnAddFrame base pre (b :: bs) x).cells 1
      ((returnAddFrame base pre (b :: bs) x).head 1) = machine.bitSym b := by
  change ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep]).getD pre.length machine.blank = _
  simp only [List.map_append,List.map_cons,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem add_return_bit_step (base : machine.Cfg) (b : Bool) (pre bs x : List Bool) :
    machine.step (returnAddFrame base pre (b :: bs) x) = returnAddFrame base (pre ++ [b]) bs x := by
  have hr := add_return_read base b pre bs x
  have hb : (returnAddFrame base pre (b :: bs) x).cells 1
      ((returnAddFrame base pre (b :: bs) x).head 1) = Sym.zero ∨
        (returnAddFrame base pre (b :: bs) x).cells 1
          ((returnAddFrame base pre (b :: bs) x).head 1) = Sym.one := by
    rw [hr]
    cases b <;> decide
  have ht := add_return_bit_transition
    (fun i => (returnAddFrame base pre (b :: bs) x).cells i ((returnAddFrame base pre (b :: bs) x).head i)) hb
  change transition (returnAddFrame base pre (b :: bs) x).state
    (fun i => (returnAddFrame base pre (b :: bs) x).cells i ((returnAddFrame base pre (b :: bs) x).head i)) = _ at ht
  apply add_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [returnAddFrame,List.append_assoc]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [returnAddFrame]

private theorem add_return_sep_transition (a : Fin 4 → Sym)
    (hp : a 1 = .sep) (hx : a 2 = .sep) : transition .rewindAdd a =
      (.advance,fun i => (a i,if i = 1 ∨ i = 2 then .left else .stay)) := by
  simp only [transition,rawTransition,hp]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · change safeStep (a 1) (a 1) .left = (a 1,.left)
    rw [hp]
    exact add_safe_left _ (by decide)
  · change safeStep (a 2) (a 2) .left = (a 2,.left)
    rw [hx]
    exact add_safe_left _ (by decide)
  · exact safe_stay _

private theorem add_return_nil_step (base : machine.Cfg) (pre x : List Bool)
    (h : x.length = pre.length) :
    machine.step (returnAddFrame base pre [] x) = arithmeticFrame base .advance pre x pre.length := by
  have hp : (returnAddFrame base pre [] x).cells 1 ((returnAddFrame base pre [] x).head 1) = Sym.sep := by
    change ((pre ++ []).map machine.bitSym ++ [Sym.sep]).getD pre.length machine.blank = _
    simp only [List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hx : (returnAddFrame base pre [] x).cells 2 ((returnAddFrame base pre [] x).head 2) = Sym.sep := by
    change (x.map machine.bitSym ++ [Sym.sep]).getD pre.length machine.blank = _
    rw [← h,List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := add_return_sep_transition
    (fun i => (returnAddFrame base pre [] x).cells i ((returnAddFrame base pre [] x).head i)) hp hx
  change transition (returnAddFrame base pre [] x).state
    (fun i => (returnAddFrame base pre [] x).cells i ((returnAddFrame base pre [] x).head i)) = _ at ht
  apply add_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp [returnAddFrame,arithmeticFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [returnAddFrame,arithmeticFrame]

private theorem add_return_run (base : machine.Cfg) (pre right x : List Bool)
    (h : x.length = pre.length + right.length) :
    machine.step^[right.length + 1] (returnAddFrame base pre right x) =
      arithmeticFrame base .advance (pre ++ right) x (pre.length + right.length) := by
  induction right generalizing pre with
  | nil => simpa using add_return_nil_step base pre x (by simpa using h)
  | cons b bs ih =>
      have ht : x.length = (pre ++ [b]).length + bs.length := by simp at *;omega
      rw [List.length_cons,Function.iterate_succ_apply,add_return_bit_step,ih _ ht]
      simp [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Fixed-width addition and complete return of both arithmetic heads. The
first-operand word is preserved exactly; all other tapes/heads retain the base. -/
private theorem add_correct (base : machine.Cfg) (c : Bool) (p x dp dx : List Bool)
    (h : p.length = x.length) (hd : dp.length = dx.length) :
    machine.step^[2 * p.length + dp.length + 2] (addFrame base c p x dp dx) =
      arithmeticFrame base .advance ((addFixed p x c).reverse ++ dp) (x.reverse ++ dx)
        (p.length + dp.length) := by
  let product := (addFixed p x c).reverse ++ dp
  let operand := x.reverse ++ dx
  have hp : product.length = p.length + dp.length := by simp [product,add_add_length p x c h]
  have hx : operand.length = product.length := by simp only [operand,hp,List.length_append,List.length_reverse];omega
  have ht : 2 * p.length + dp.length + 2 = (product.length + 1 + 1) + p.length := by omega
  rw [ht,Function.iterate_add_apply,add_add_run base c p x dp dx h,
    Function.iterate_succ_apply,add_add_nil_step,add_return_run base [] product operand (by simpa using hx)]
  simp only [List.nil_append,List.length_nil,Nat.zero_add]
  rw [hp]

end IntMul.TapeSchoolbook



namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)
open IntMul.BinarySchoolbook (shiftCarry addFixed advanceWord foldWord)

private theorem loop_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem loop_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem loop_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem loop_padded_length (x : List Bool) :
    (List.replicate x.length false ++ x).length = 2 * x.length := by simp;omega

private theorem loop_product_ready_frame (x y old p : List Bool) (j : ℕ) (q₀ q : State) :
    productFrame (readyFrame x y old j q₀) q p p.length = readyFrame x y p j q := by
  apply loop_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [productFrame,readyFrame]
  · funext i
    fin_cases i <;> simp [productFrame,readyFrame]

private theorem loop_arithmetic_ready_frame (x y old p : List Bool) (j : ℕ) (q₀ q : State)
    (hp : p.length = 2 * x.length) :
    arithmeticFrame (readyFrame x y old j q₀) q p (List.replicate x.length false ++ x) (2 * x.length) =
      readyFrame x y p j q := by
  apply loop_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [arithmeticFrame,readyFrame]
  · funext i
    fin_cases i <;> simp [arithmeticFrame,readyFrame,hp]

private theorem loop_shift_start_frame (x y p : List Bool) (j : ℕ) (b : Bool) :
    shiftFrame (readyFrame x y p j .next) b false p.reverse [] =
      readyFrame x y p j (.shift b false) := by
  apply loop_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [shiftFrame,readyFrame]
  · funext i
    fin_cases i <;> simp [shiftFrame,readyFrame]

private theorem loop_shift_ready (x y p : List Bool) (j : ℕ) (b : Bool) :
    machine.step^[2 * p.length + 2] (readyFrame x y p j (.shift b false)) =
      readyFrame x y (shiftCarry false p.reverse).reverse j (if b then .add false else .advance) := by
  have hs := shift_correct (readyFrame x y p j .next) b false p.reverse []
  simp only [List.length_reverse,List.length_nil,Nat.add_zero,List.append_nil] at hs
  rw [loop_shift_start_frame] at hs
  have hl : (shiftCarry false p.reverse).reverse.length = p.length := by
    simp [BinarySchoolbook.shift_length]
  rw [← hl,loop_product_ready_frame] at hs
  simpa only [hl] using hs

private theorem loop_add_start_frame (x y p : List Bool) (j : ℕ) (hp : p.length = 2 * x.length) :
    addFrame (readyFrame x y p j (.add false)) false p.reverse
      (List.replicate x.length false ++ x).reverse [] [] = readyFrame x y p j (.add false) := by
  apply loop_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [addFrame,readyFrame]
  · funext i
    fin_cases i <;> simp [addFrame,readyFrame,hp,loop_padded_length] <;> omega

private theorem loop_add_ready (x y p : List Bool) (j : ℕ) (hp : p.length = 2 * x.length) :
    machine.step^[2 * p.length + 2] (readyFrame x y p j (.add false)) =
      readyFrame x y (addFixed p.reverse (List.replicate x.length false ++ x).reverse false).reverse j .advance := by
  have hw : p.reverse.length = (List.replicate x.length false ++ x).reverse.length := by
    simpa only [List.length_reverse,loop_padded_length] using hp
  have hs := add_correct (readyFrame x y p j (.add false)) false p.reverse
    (List.replicate x.length false ++ x).reverse [] [] hw rfl
  simp only [List.length_reverse,List.length_nil,Nat.add_zero,List.append_nil,List.reverse_reverse] at hs
  rw [loop_add_start_frame x y p j hp] at hs
  have hl : (addFixed p.reverse (List.replicate x.length false ++ x).reverse false).reverse.length = 2 * x.length := by
    rw [List.length_reverse,BinarySchoolbook.add_fixed_length _ _ _ hw,List.length_reverse,hp]
  rw [hp,loop_arithmetic_ready_frame x y p _ j (.add false) .advance hl] at hs
  simpa only [hp] using hs

private theorem loop_next_bit_transition (a : Fin 4 → Sym) (b : Bool) (h : a 3 = machine.bitSym b) :
    transition .next a = (.shift b false,fun i => (a i,.stay)) := by
  have hb : a 3 = Sym.zero ∨ a 3 = Sym.one := by rw [h];cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  · rw [h]
    cases b <;> rfl
  · funext i
    exact safe_stay _

private theorem loop_next_bit_step (x y p : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (readyFrame x y p j .next) = readyFrame x y p j (.shift y[j] false) := by
  have hr : (readyFrame x y p j .next).cells 3 ((readyFrame x y p j .next).head 3) = machine.bitSym y[j] := by
    change (y.map machine.bitSym ++ [Sym.sep]).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have ht := loop_next_bit_transition
    (fun i => (readyFrame x y p j .next).cells i ((readyFrame x y p j .next).head i)) y[j] hr
  change transition (readyFrame x y p j .next).state
    (fun i => (readyFrame x y p j .next).cells i ((readyFrame x y p j .next).head i)) = _ at ht
  apply loop_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem loop_advance_transition (a : Fin 4 → Sym) :
    transition .advance a = (.next,fun i => (a i,if i = 3 then .right else .stay)) := by
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : i = 3
  · simp only [if_pos hi,loop_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem loop_advance_step (x y p : List Bool) (j : ℕ) :
    machine.step (readyFrame x y p j .advance) = readyFrame x y p (j + 1) .next := by
  have ht := loop_advance_transition
    (fun i => (readyFrame x y p j .advance).cells i ((readyFrame x y p j .advance).head i))
  change transition (readyFrame x y p j .advance).state
    (fun i => (readyFrame x y p j .advance).cells i ((readyFrame x y p j .advance).head i)) = _ at ht
  apply loop_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [readyFrame]

/-- One actual most-significant-first multiplication-bit cycle, including all
shift, optional add, head returns, and multiplier-head dispatch transitions. -/
private theorem iteration_correct (x y p : List Bool) (j : ℕ)
    (hj : j < y.length) (hp : p.length = 2 * x.length) :
    machine.step^[iterationSteps p.length y[j]] (readyFrame x y p j .next) =
      readyFrame x y
        (advanceWord (List.replicate x.length false ++ x).reverse p.reverse y[j]).reverse
          (j + 1) .next := by
  let shifted := (shiftCarry false p.reverse).reverse
  have hslen : shifted.length = p.length := by simp [shifted,BinarySchoolbook.shift_length]
  have hs : machine.step^[2 * p.length + 3] (readyFrame x y p j .next) =
      readyFrame x y shifted j (if y[j] then .add false else .advance) := by
    rw [show 2 * p.length + 3 = (2 * p.length + 2) + 1 by omega,
      Function.iterate_add_apply,Function.iterate_one,loop_next_bit_step x y p j hj,loop_shift_ready]
  cases hb : y[j] with
  | false =>
      simp only [iterationSteps,hb,advanceWord,Bool.false_eq_true,if_false,if_true,if_pos rfl] at hs ⊢
      rw [show 2 * p.length + 4 = 1 + (2 * p.length + 3) by omega,
        Function.iterate_add_apply,hs,Function.iterate_one,loop_advance_step]
  | true =>
      have ha := loop_add_ready x y shifted j (by rw [hslen,hp])
      rw [hslen] at ha
      simp only [iterationSteps,hb,advanceWord,Bool.false_eq_true,if_false,if_true,if_pos rfl] at hs ⊢
      rw [show 4 * p.length + 6 = 1 + ((2 * p.length + 2) + (2 * p.length + 3)) by omega,
        Function.iterate_add_apply,Function.iterate_add_apply,hs,ha,Function.iterate_one,loop_advance_step]
      simp [shifted]

/-- The same fixed loop processes an arbitrary remaining multiplier suffix.
The caller's prefix is retained on the saved multiplier tape. -/
private theorem loop_correct (x pre rest p : List Bool) (hp : p.length = 2 * x.length) :
    machine.step^[loopSteps (2 * x.length) rest]
      (readyFrame x (pre ++ rest) p.reverse pre.length .next) =
        readyFrame x (pre ++ rest)
          (foldWord (List.replicate x.length false ++ x).reverse rest p).reverse
            (pre.length + rest.length) .next := by
  induction rest generalizing pre p with
  | nil => simp [loopSteps,foldWord]
  | cons b bs ih =>
      have hj : pre.length < (pre ++ b :: bs).length := by simp
      have hr : (pre ++ b :: bs)[pre.length] = b := by
        have hd : (pre ++ b :: bs).getD pre.length false = b := by
          rw [List.getD_append_right _ _ _ _ (by omega)]
          simp
        rw [List.getD_eq_getElem _ _ hj] at hd
        exact hd
      have hc := iteration_correct x (pre ++ b :: bs) p.reverse pre.length hj (by simpa using hp)
      rw [hr,List.length_reverse,hp,List.reverse_reverse] at hc
      have hn : (advanceWord (List.replicate x.length false ++ x).reverse p b).length = 2 * x.length := by
        rw [BinarySchoolbook.advance_length _ _ _ (by simp [loop_padded_length,hp] <;> omega),List.length_reverse,loop_padded_length]
      rw [show loopSteps (2 * x.length) (b :: bs) =
          loopSteps (2 * x.length) bs + iterationSteps (2 * x.length) b by
            rw [loopSteps,Nat.add_comm],Function.iterate_add_apply,hc]
      have ht := ih (pre ++ [b]) (advanceWord (List.replicate x.length false ++ x).reverse p b) hn
      simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,
        List.length_cons,List.length_nil,Nat.zero_add,foldWord,List.foldl_cons,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

private theorem loop_steps_bound (width : ℕ) (y : List Bool) :
    loopSteps width y ≤ (4 * width + 6) * y.length := by
  induction y with
  | nil => simp [loopSteps]
  | cons b bs ih =>
      have hb : iterationSteps width b ≤ 4 * width + 6 := by cases b <;> simp [iterationSteps] <;> omega
      simp only [loopSteps,List.length_cons,Nat.mul_succ]
      omega

end IntMul.TapeSchoolbook



namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem setup_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem setup_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem setup_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem setup_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ w.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private def setup_padFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .padX
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 ∨ i = 2 then machine.tapeOf ((List.replicate j false).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 ∨ i = 1 ∨ i = 2 then j + 1 else 1

private def setup_inputReturnFrame (x y : List Bool) (pos : ℕ) : machine.Cfg where
  state := .rewindInput
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 ∨ i = 2 then machine.tapeOf ((List.replicate x.length false).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then pos else if i = 1 ∨ i = 2 then x.length + 1 else 1

private def setup_copyXFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyX
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((List.replicate (x.length + j) false).map machine.bitSym)
    else if i = 2 then machine.tapeOf ((List.replicate x.length false ++ x.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then j + 1 else if i = 1 ∨ i = 2 then x.length + j + 1 else 1

private def setup_copyYFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyY
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((List.replicate (2 * x.length) false).map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf ((List.replicate x.length false ++ x).map machine.bitSym ++ [Sym.sep])
    else machine.tapeOf ((y.take j).map machine.bitSym)
  head := fun i => if i = 0 then x.length + j + 2 else if i = 1 ∨ i = 2 then 2 * x.length else j + 1

private def setup_multiplierReturnFrame (x y : List Bool) (pos : ℕ) : machine.Cfg where
  state := .rewindY
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((List.replicate (2 * x.length) false).map machine.bitSym ++ [Sym.sep])
    else if i = 2 then machine.tapeOf ((List.replicate x.length false ++ x).map machine.bitSym ++ [Sym.sep])
    else machine.tapeOf (y.map machine.bitSym ++ [Sym.sep])
  head := fun i => if i = 0 then x.length + y.length + 2 else if i = 1 ∨ i = 2 then 2 * x.length else pos

private theorem setup_initial_transition (a : Fin 4 → Sym) :
    transition .start a = (.padX,fun i => (a i,.right)) := by
  simp [transition,rawTransition,setup_safe_right]

private theorem setup_initial_step (x y : List Bool) : machine.step (machine.initCfg x y) = setup_padFrame x y 0 := by
  have ht := setup_initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self 0 _
    all_goals
      change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
      exact Function.update_eq_self 0 _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem setup_pad_bit_transition (a : Fin 4 → Sym) (b : Bool)
    (h : a 0 = machine.bitSym b) (h₁ : a 1 = .blank) (h₂ : a 2 = .blank) :
    transition .padX a = (.padX,fun i =>
      (if i = 1 ∨ i = 2 then .zero else a i,if i = 0 ∨ i = 1 ∨ i = 2 then .right else .stay)) := by
  have hb : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [h];cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact setup_safe_right _
  · change safeStep (a 1) .zero .right = (.zero,.right)
    rw [h₁]
    decide
  · change safeStep (a 2) .zero .right = (.zero,.right)
    rw [h₂]
    decide
  · exact safe_stay _

private theorem setup_pad_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (setup_padFrame x y j) = setup_padFrame x y (j + 1) := by
  have hr : (setup_padFrame x y j).cells 0 ((setup_padFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hw : ∀ i : Fin 4, i = 1 ∨ i = 2 → (setup_padFrame x y j).cells i ((setup_padFrame x y j).head i) = Sym.blank := by
    intro i hi
    rcases hi with rfl | rfl
    all_goals
      change ((List.replicate j false).map machine.bitSym).getD j machine.blank = _
      exact List.getD_eq_default _ _ (by simp)
  have ht := setup_pad_bit_transition
    (fun i => (setup_padFrame x y j).cells i ((setup_padFrame x y j).head i)) x[j] hr
      (hw 1 (by simp)) (hw 2 (by simp))
  change transition (setup_padFrame x y j).state
    (fun i => (setup_padFrame x y j).cells i ((setup_padFrame x y j).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((List.replicate j false).map machine.bitSym)) (j + 1) Sym.zero =
        machine.tapeOf ((List.replicate (j + 1) false).map machine.bitSym)
      simpa only [List.length_map,List.length_replicate,List.replicate_succ',List.map_append,
        List.map_singleton,MultitapeTM.bitSym,Bool.false_eq_true,if_false] using
          setup_tapeOf_append_one machine ((List.replicate j false).map machine.bitSym) Sym.zero
    · change Function.update (machine.tapeOf ((List.replicate j false).map machine.bitSym)) (j + 1) Sym.zero =
        machine.tapeOf ((List.replicate (j + 1) false).map machine.bitSym)
      simpa only [List.length_map,List.length_replicate,List.replicate_succ',List.map_append,
        List.map_singleton,MultitapeTM.bitSym,Bool.false_eq_true,if_false] using
          setup_tapeOf_append_one machine ((List.replicate j false).map machine.bitSym) Sym.zero
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_padFrame]

private theorem setup_pad_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = setup_padFrame x y j := by
  induction j with
  | zero => simpa using setup_initial_step x y
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),setup_pad_step x y j (by omega)]

private theorem setup_pad_end_transition (a : Fin 4 → Sym) (h : a 0 = .sep) :
    transition .padX a = (.rewindInput,fun i => (a i,if i = 0 then .left else .stay)) := by
  simp only [transition,rawTransition,h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    rw [h]
    exact setup_safe_left _ (by decide)
  · simp only [if_neg hi,safe_stay]

private theorem setup_pad_end_step (x y : List Bool) :
    machine.step (setup_padFrame x y x.length) = setup_inputReturnFrame x y x.length := by
  have hr : (setup_padFrame x y x.length).cells 0 ((setup_padFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := setup_pad_end_transition
    (fun i => (setup_padFrame x y x.length).cells i ((setup_padFrame x y x.length).head i)) hr
  change transition (setup_padFrame x y x.length).state
    (fun i => (setup_padFrame x y x.length).cells i ((setup_padFrame x y x.length).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [setup_padFrame,setup_inputReturnFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_padFrame,setup_inputReturnFrame]

private theorem setup_input_left_transition (a : Fin 4 → Sym) (h : a 0 ≠ .start) :
    transition .rewindInput a = (.rewindInput,fun i => (a i,if i = 0 then .left else .stay)) := by
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    exact setup_safe_left _ h
  · simp only [if_neg hi,safe_stay]

private theorem setup_input_left_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (setup_inputReturnFrame x y (j + 1)) = setup_inputReturnFrame x y j := by
  have hr : (setup_inputReturnFrame x y (j + 1)).cells 0
      ((setup_inputReturnFrame x y (j + 1)).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hn : (setup_inputReturnFrame x y (j + 1)).cells 0
      ((setup_inputReturnFrame x y (j + 1)).head 0) ≠ Sym.start := by rw [hr];cases x[j] <;> decide
  have ht := setup_input_left_transition
    (fun i => (setup_inputReturnFrame x y (j + 1)).cells i ((setup_inputReturnFrame x y (j + 1)).head i)) hn
  change transition (setup_inputReturnFrame x y (j + 1)).state
    (fun i => (setup_inputReturnFrame x y (j + 1)).cells i ((setup_inputReturnFrame x y (j + 1)).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_inputReturnFrame]

private theorem setup_input_marker_transition (a : Fin 4 → Sym) (h : a 0 = .start) :
    transition .rewindInput a = (.copyX,fun i => (a i,if i = 0 then .right else .stay)) := by
  simp only [transition,rawTransition,h,if_true]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi,setup_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem setup_input_marker_step (x y : List Bool) :
    machine.step (setup_inputReturnFrame x y 0) = setup_copyXFrame x y 0 := by
  have ht := setup_input_marker_transition
    (fun i => (setup_inputReturnFrame x y 0).cells i ((setup_inputReturnFrame x y 0).head i)) rfl
  change transition (setup_inputReturnFrame x y 0).state
    (fun i => (setup_inputReturnFrame x y 0).cells i ((setup_inputReturnFrame x y 0).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [setup_inputReturnFrame,setup_copyXFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_inputReturnFrame,setup_copyXFrame]

private theorem setup_input_return_run (x y : List Bool) (pos : ℕ) (hp : pos ≤ x.length) :
    machine.step^[pos + 1] (setup_inputReturnFrame x y pos) = setup_copyXFrame x y 0 := by
  induction pos with
  | zero => simpa using setup_input_marker_step x y
  | succ pos ih => rw [Function.iterate_succ_apply,setup_input_left_step x y pos (by omega),ih (by omega)]

private theorem setup_copy_x_transition (a : Fin 4 → Sym) (b : Bool)
    (h : a 0 = machine.bitSym b) (h₁ : a 1 = .blank) (h₂ : a 2 = .blank) :
    transition .copyX a = (.copyX,fun i =>
      (if i = 1 then .zero else if i = 2 then machine.bitSym b else a i,
        if i = 0 ∨ i = 1 ∨ i = 2 then .right else .stay)) := by
  have hb : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [h];cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact setup_safe_right _
  · change safeStep (a 1) .zero .right = (.zero,.right)
    rw [h₁]
    decide
  · change safeStep (a 2) (a 0) .right = (machine.bitSym b,.right)
    rw [h₂,h]
    cases b <;> decide
  · exact safe_stay _

private theorem setup_copy_x_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (setup_copyXFrame x y j) = setup_copyXFrame x y (j + 1) := by
  have hr : (setup_copyXFrame x y j).cells 0 ((setup_copyXFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (List.replicate x.length false ++ x.take j).length = x.length + j := by
    simp [Nat.min_eq_left hj.le]
  have h₁ : (setup_copyXFrame x y j).cells 1 ((setup_copyXFrame x y j).head 1) = Sym.blank := by
    change ((List.replicate (x.length + j) false).map machine.bitSym).getD (x.length + j) machine.blank = _
    exact List.getD_eq_default _ _ (by simp)
  have h₂ : (setup_copyXFrame x y j).cells 2 ((setup_copyXFrame x y j).head 2) = Sym.blank := by
    change ((List.replicate x.length false ++ x.take j).map machine.bitSym).getD (x.length + j) machine.blank = _
    exact List.getD_eq_default _ _ (by simp [hl])
  have ht := setup_copy_x_transition
    (fun i => (setup_copyXFrame x y j).cells i ((setup_copyXFrame x y j).head i)) x[j] hr h₁ h₂
  change transition (setup_copyXFrame x y j).state
    (fun i => (setup_copyXFrame x y j).cells i ((setup_copyXFrame x y j).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((List.replicate (x.length + j) false).map machine.bitSym))
        (x.length + j + 1) Sym.zero =
          machine.tapeOf ((List.replicate (x.length + (j + 1)) false).map machine.bitSym)
      rw [show x.length + (j + 1) = (x.length + j) + 1 by omega]
      simpa only [List.length_map,List.length_replicate,List.replicate_succ',List.map_append,
        List.map_singleton,MultitapeTM.bitSym,Bool.false_eq_true,if_false] using
          setup_tapeOf_append_one machine ((List.replicate (x.length + j) false).map machine.bitSym) Sym.zero
    · change Function.update (machine.tapeOf ((List.replicate x.length false ++ x.take j).map machine.bitSym))
        (x.length + j + 1) (machine.bitSym x[j]) =
          machine.tapeOf ((List.replicate x.length false ++ x.take (j + 1)).map machine.bitSym)
      rw [List.take_succ_eq_append_getElem hj,← List.append_assoc]
      have hs := setup_tapeOf_append_one machine ((List.replicate x.length false ++ x.take j).map machine.bitSym)
        (machine.bitSym x[j])
      rw [List.length_map,hl] at hs
      simpa only [List.map_append,List.map_singleton] using hs
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_copyXFrame] <;> omega

private theorem setup_copy_x_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j] (setup_copyXFrame x y 0) = setup_copyXFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),setup_copy_x_step x y j (by omega)]

private theorem setup_copy_x_end_transition (a : Fin 4 → Sym)
    (h : a 0 = .sep) (h₁ : a 1 = .blank) (h₂ : a 2 = .blank) :
    transition .copyX a = (.copyY,fun i =>
      (if i = 1 ∨ i = 2 then .sep else a i,
        if i = 0 then .right else if i = 1 ∨ i = 2 then .left else .stay)) := by
  simp only [transition,rawTransition,h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · exact setup_safe_right _
  · change safeStep (a 1) .sep .left = (.sep,.left)
    rw [h₁]
    decide
  · change safeStep (a 2) .sep .left = (.sep,.left)
    rw [h₂]
    decide
  · exact safe_stay _

private theorem setup_copy_x_end_step (x y : List Bool) :
    machine.step (setup_copyXFrame x y x.length) = setup_copyYFrame x y 0 := by
  have hr : (setup_copyXFrame x y x.length).cells 0 ((setup_copyXFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have h₁ : (setup_copyXFrame x y x.length).cells 1 ((setup_copyXFrame x y x.length).head 1) = Sym.blank := by
    change ((List.replicate (x.length + x.length) false).map machine.bitSym).getD (x.length + x.length) machine.blank = _
    exact List.getD_eq_default _ _ (by simp)
  have h₂ : (setup_copyXFrame x y x.length).cells 2 ((setup_copyXFrame x y x.length).head 2) = Sym.blank := by
    change ((List.replicate x.length false ++ x.take x.length).map machine.bitSym).getD (x.length + x.length) machine.blank = _
    exact List.getD_eq_default _ _ (by simp)
  have ht := setup_copy_x_end_transition
    (fun i => (setup_copyXFrame x y x.length).cells i ((setup_copyXFrame x y x.length).head i)) hr h₁ h₂
  change transition (setup_copyXFrame x y x.length).state
    (fun i => (setup_copyXFrame x y x.length).cells i ((setup_copyXFrame x y x.length).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((List.replicate (x.length + x.length) false).map machine.bitSym))
        (x.length + x.length + 1) Sym.sep =
          machine.tapeOf ((List.replicate (2 * x.length) false).map machine.bitSym ++ [Sym.sep])
      rw [show 2 * x.length = x.length + x.length by omega]
      simpa only [List.length_map,List.length_replicate] using
        setup_tapeOf_append_one machine ((List.replicate (x.length + x.length) false).map machine.bitSym) Sym.sep
    · change Function.update (machine.tapeOf ((List.replicate x.length false ++ x.take x.length).map machine.bitSym))
        (x.length + x.length + 1) Sym.sep =
          machine.tapeOf ((List.replicate x.length false ++ x).map machine.bitSym ++ [Sym.sep])
      simp only [List.take_length]
      simpa only [List.length_map,List.length_append,List.length_replicate] using
        setup_tapeOf_append_one machine ((List.replicate x.length false ++ x).map machine.bitSym) Sym.sep
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_copyXFrame,setup_copyYFrame] <;> omega

private theorem setup_copy_y_transition (a : Fin 4 → Sym) (b : Bool)
    (h : a 0 = machine.bitSym b) (h₃ : a 3 = .blank) :
    transition .copyY a = (.copyY,fun i =>
      (if i = 3 then machine.bitSym b else a i,if i = 0 ∨ i = 3 then .right else .stay)) := by
  have hb : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [h]; cases b <;> decide
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact setup_safe_right _
  · exact safe_stay _
  · exact safe_stay _
  · change safeStep (a 3) (a 0) .right = (machine.bitSym b,.right)
    rw [h₃,h]
    cases b <;> decide

private theorem setup_copy_y_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (setup_copyYFrame x y j) = setup_copyYFrame x y (j + 1) := by
  have hr : (setup_copyYFrame x y j).cells 0 ((setup_copyYFrame x y j).head 0) = machine.bitSym y[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD
      (x.length + j + 1) machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map,show x.length + j + 1 - x.length = j + 1 by omega,List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (y.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have h₃ : (setup_copyYFrame x y j).cells 3 ((setup_copyYFrame x y j).head 3) = Sym.blank := by
    change ((y.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ (by simp [hl])
  have ht := setup_copy_y_transition
    (fun i => (setup_copyYFrame x y j).cells i ((setup_copyYFrame x y j).head i)) y[j] hr h₃
  change transition (setup_copyYFrame x y j).state
    (fun i => (setup_copyYFrame x y j).cells i ((setup_copyYFrame x y j).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((y.take j).map machine.bitSym)) (j + 1)
        (machine.bitSym y[j]) = machine.tapeOf ((y.take (j + 1)).map machine.bitSym)
      rw [List.take_succ_eq_append_getElem hj,List.map_append,List.map_singleton]
      have hs := setup_tapeOf_append_one machine ((y.take j).map machine.bitSym) (machine.bitSym y[j])
      rw [List.length_map,hl] at hs
      exact hs
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_copyYFrame] <;> omega

private theorem setup_copy_y_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (setup_copyYFrame x y 0) = setup_copyYFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),setup_copy_y_step x y j (by omega)]

private theorem setup_copy_y_end_transition (a : Fin 4 → Sym)
    (h : a 0 = .blank) (h₃ : a 3 = .blank) :
    transition .copyY a = (.rewindY,fun i =>
      (if i = 3 then .sep else a i,if i = 3 then .left else .stay)) := by
  simp only [transition,rawTransition,h]
  rw [if_neg (by decide : ¬(Sym.blank = Sym.zero ∨ Sym.blank = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · change safeStep (a 3) .sep .left = (.sep,.left)
    rw [h₃]
    decide

private theorem setup_copy_y_end_step (x y : List Bool) :
    machine.step (setup_copyYFrame x y y.length) = setup_multiplierReturnFrame x y y.length := by
  have hr : (setup_copyYFrame x y y.length).cells 0 ((setup_copyYFrame x y y.length).head 0) = Sym.blank := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD
      (x.length + y.length + 1) machine.blank = _
    exact List.getD_eq_default _ _ (by simp; omega)
  have h₃ : (setup_copyYFrame x y y.length).cells 3 ((setup_copyYFrame x y y.length).head 3) = Sym.blank := by
    change ((y.take y.length).map machine.bitSym).getD y.length machine.blank = _
    exact List.getD_eq_default _ _ (by simp)
  have ht := setup_copy_y_end_transition
    (fun i => (setup_copyYFrame x y y.length).cells i ((setup_copyYFrame x y y.length).head i)) hr h₃
  change transition (setup_copyYFrame x y y.length).state
    (fun i => (setup_copyYFrame x y y.length).cells i ((setup_copyYFrame x y y.length).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf ((y.take y.length).map machine.bitSym))
        (y.length + 1) Sym.sep = machine.tapeOf (y.map machine.bitSym ++ [Sym.sep])
      simp only [List.take_length]
      simpa only [List.length_map] using setup_tapeOf_append_one machine (y.map machine.bitSym) Sym.sep
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_copyYFrame,setup_multiplierReturnFrame]

private theorem setup_multiplier_left_transition (a : Fin 4 → Sym) (h : a 3 ≠ .start) :
    transition .rewindY a = (.rewindY,fun i => (a i,if i = 3 then .left else .stay)) := by
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i = 3
  · subst i
    simp only [if_pos rfl]
    exact setup_safe_left _ h
  · simp only [if_neg hi,safe_stay]

private theorem setup_multiplier_left_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (setup_multiplierReturnFrame x y (j + 1)) = setup_multiplierReturnFrame x y j := by
  have hr : (setup_multiplierReturnFrame x y (j + 1)).cells 3
      ((setup_multiplierReturnFrame x y (j + 1)).head 3) = machine.bitSym y[j] := by
    change (y.map machine.bitSym ++ [Sym.sep]).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hn : (setup_multiplierReturnFrame x y (j + 1)).cells 3
      ((setup_multiplierReturnFrame x y (j + 1)).head 3) ≠ Sym.start := by rw [hr]; cases y[j] <;> decide
  have ht := setup_multiplier_left_transition
    (fun i => (setup_multiplierReturnFrame x y (j + 1)).cells i ((setup_multiplierReturnFrame x y (j + 1)).head i)) hn
  change transition (setup_multiplierReturnFrame x y (j + 1)).state
    (fun i => (setup_multiplierReturnFrame x y (j + 1)).cells i ((setup_multiplierReturnFrame x y (j + 1)).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_multiplierReturnFrame]

private theorem setup_multiplier_marker_transition (a : Fin 4 → Sym) (h : a 3 = .start) :
    transition .rewindY a = (.next,fun i => (a i,if i = 3 then .right else .stay)) := by
  simp only [transition,rawTransition,h,if_true]
  congr 1
  funext i
  by_cases hi : i = 3
  · simp only [if_pos hi,setup_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem setup_multiplier_marker_step (x y : List Bool) :
    machine.step (setup_multiplierReturnFrame x y 0) =
      readyFrame x y (List.replicate (2 * x.length) false) 0 .next := by
  have ht := setup_multiplier_marker_transition
    (fun i => (setup_multiplierReturnFrame x y 0).cells i ((setup_multiplierReturnFrame x y 0).head i)) rfl
  change transition (setup_multiplierReturnFrame x y 0).state
    (fun i => (setup_multiplierReturnFrame x y 0).cells i ((setup_multiplierReturnFrame x y 0).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [setup_multiplierReturnFrame,readyFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [setup_multiplierReturnFrame,readyFrame]

private theorem setup_multiplier_return_run (x y : List Bool) (pos : ℕ) (hp : pos ≤ y.length) :
    machine.step^[pos + 1] (setup_multiplierReturnFrame x y pos) =
      readyFrame x y (List.replicate (2 * x.length) false) 0 .next := by
  induction pos with
  | zero => simpa using setup_multiplier_marker_step x y
  | succ pos ih => rw [Function.iterate_succ_apply,setup_multiplier_left_step x y pos (by omega),ih (by omega)]

/-- Exact input setup, including padding, both operand copies, separator
writes, and the two head returns. No width or well-formedness promise is used. -/
private theorem setup_correct (x y : List Bool) :
    machine.step^[3 * x.length + 2 * y.length + 6] (machine.initCfg x y) =
      readyFrame x y (List.replicate (2 * x.length) false) 0 .next := by
  have hpad : machine.step^[x.length + 2] (machine.initCfg x y) =
      setup_inputReturnFrame x y x.length := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply',setup_pad_run x y x.length le_rfl,setup_pad_end_step]
  have hreturn : machine.step^[2 * x.length + 3] (machine.initCfg x y) = setup_copyXFrame x y 0 := by
    rw [show 2 * x.length + 3 = (x.length + 1) + (x.length + 2) by omega,
      Function.iterate_add_apply,hpad,setup_input_return_run x y x.length le_rfl]
  have hcopyX : machine.step^[3 * x.length + 4] (machine.initCfg x y) = setup_copyYFrame x y 0 := by
    rw [show 3 * x.length + 4 = (x.length + (2 * x.length + 3)) + 1 by omega,
      Function.iterate_succ_apply',Function.iterate_add_apply,hreturn,
      setup_copy_x_run x y x.length le_rfl,setup_copy_x_end_step]
  have hcopyY : machine.step^[3 * x.length + y.length + 5] (machine.initCfg x y) =
      setup_multiplierReturnFrame x y y.length := by
    rw [show 3 * x.length + y.length + 5 = (y.length + (3 * x.length + 4)) + 1 by omega,
      Function.iterate_succ_apply',Function.iterate_add_apply,hcopyX,
      setup_copy_y_run x y y.length le_rfl,setup_copy_y_end_step]
  rw [show 3 * x.length + 2 * y.length + 6 =
      (y.length + 1) + (3 * x.length + y.length + 5) by omega,
    Function.iterate_add_apply,hcopyY,setup_multiplier_return_run x y y.length le_rfl]

end IntMul.TapeSchoolbook



namespace IntMul.TapeSchoolbook

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem output_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem output_safe_right (s : Sym) : safeStep s s .right = (s,.right) := by
  by_cases hs : s = .start <;> simp [safeStep,hs]

private theorem output_tape_erase_end (M : MultitapeTM) (word : List M.Sym) (endSymbol : M.Sym) :
    Function.update (M.tapeOf (word ++ [endSymbol])) (word.length + 1) M.blank = M.tapeOf word := by
  funext pos
  cases pos with
  | zero => simp [MultitapeTM.tapeOf]
  | succ pos =>
      by_cases he : pos = word.length
      · subst pos
        simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : pos + 1 ≠ word.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : pos < word.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : word.length ≤ pos := by omega
          rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
          exact List.getD_eq_default _ _ (by simp;omega)

private def output_eraseFrame (x y p : List Bool) : machine.Cfg where
  state := .erase
  cells := (readyFrame x y p y.length .next).cells
  head := fun i => if i = 1 then p.length + 1 else (readyFrame x y p y.length .next).head i

private theorem output_next_end_transition (a : Fin 4 → Sym) (h : a 3 = .sep) :
    transition .next a = (.erase,fun i => (a i,if i = 1 then .right else .stay)) := by
  simp only [transition,rawTransition,h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  by_cases hi : i = 1
  · simp only [if_pos hi,output_safe_right]
  · simp only [if_neg hi,safe_stay]

private theorem output_next_end_step (x y p : List Bool) :
    machine.step (readyFrame x y p y.length .next) = output_eraseFrame x y p := by
  have hr : (readyFrame x y p y.length .next).cells 3
      ((readyFrame x y p y.length .next).head 3) = Sym.sep := by
    change (y.map machine.bitSym ++ [Sym.sep]).getD y.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := output_next_end_transition
    (fun i => (readyFrame x y p y.length .next).cells i ((readyFrame x y p y.length .next).head i)) hr
  change transition (readyFrame x y p y.length .next).state
    (fun i => (readyFrame x y p y.length .next).cells i ((readyFrame x y p y.length .next).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1 <;> simp [output_eraseFrame,readyFrame,hi]

private theorem output_erase_transition (a : Fin 4 → Sym) (h : a 1 = .sep) :
    transition .erase a = (.halt,fun i => (if i = 1 then .blank else a i,.stay)) := by
  simp only [transition,rawTransition]
  congr 1
  funext i
  by_cases hi : i = 1
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi,safe_stay]

private theorem output_erase_step (x y p : List Bool) : machine.step (output_eraseFrame x y p) = finalFrame x y p := by
  have hr : (output_eraseFrame x y p).cells 1 ((output_eraseFrame x y p).head 1) = Sym.sep := by
    change (p.map machine.bitSym ++ [Sym.sep]).getD p.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := output_erase_transition
    (fun i => (output_eraseFrame x y p).cells i ((output_eraseFrame x y p).head i)) hr
  change transition (output_eraseFrame x y p).state
    (fun i => (output_eraseFrame x y p).cells i ((output_eraseFrame x y p).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = 1
    · subst i
      change Function.update (machine.tapeOf (p.map machine.bitSym ++ [Sym.sep]))
        (p.length + 1) Sym.blank = machine.tapeOf (p.map machine.bitSym)
      simpa only [List.length_map] using output_tape_erase_end machine (p.map machine.bitSym) Sym.sep
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp [output_eraseFrame,finalFrame,readyFrame,hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [output_eraseFrame,finalFrame,readyFrame]

/-- One delimiter dispatch and one physical erase leave an exact output tape
with the product bits, start marker, and blanks everywhere after the word. -/
private theorem finish_correct (x y p : List Bool) :
    machine.step^[2] (readyFrame x y p y.length .next) = finalFrame x y p := by
  change machine.step (machine.step (readyFrame x y p y.length .next)) = _
  rw [output_next_end_step,output_erase_step]

end IntMul.TapeSchoolbook



namespace IntMul.TapeSchoolbook

/-- Every setup, arithmetic, return, dispatch, and final erase transition is
included in this proof-side clock. The machine does not consult the clock. -/
private def main_totalSteps (x y : List Bool) : ℕ :=
  3 * x.length + 2 * y.length + 6 + loopSteps (2 * x.length) y + 2

private theorem run_correct (x y : List Bool) :
    machine.step^[main_totalSteps x y] (machine.initCfg x y) =
      finalFrame x y (BinarySchoolbook.productWord x y) := by
  have hl := loop_correct x [] y (List.replicate (2 * x.length) false) (by simp)
  simp only [List.nil_append,List.length_nil,List.reverse_replicate,Nat.zero_add] at hl
  change machine.step^[loopSteps (2 * x.length) y]
    (readyFrame x y (List.replicate (2 * x.length) false) 0 .next) =
      readyFrame x y (BinarySchoolbook.productWord x y) y.length .next at hl
  rw [show main_totalSteps x y =
      2 + (loopSteps (2 * x.length) y + (3 * x.length + 2 * y.length + 6)) by
        unfold main_totalSteps; omega,
    Function.iterate_add_apply,Function.iterate_add_apply,setup_correct,hl,finish_correct]

private theorem halts_correct (x y : List Bool) :
    machine.HaltsWithOutput x y (main_totalSteps x y) (BinarySchoolbook.productWord x y) := by
  rw [MultitapeTM.HaltsWithOutput,run_correct]
  constructor <;> rfl

private theorem main_total_steps_bound (x y : List Bool) :
    main_totalSteps x y ≤ 3 * x.length + 2 * y.length + 8 +
      (8 * x.length + 6) * y.length := by
  have h := loop_steps_bound (2 * x.length) y
  rw [show 4 * (2 * x.length) + 6 = 8 * x.length + 6 by omega] at h
  unfold main_totalSteps
  omega

private theorem multiplies_at (n : ℕ) (hn : 1 ≤ n) :
    MultipliesAt machine n (32 * (n : ℝ)^2) := by
  intro x y hx hy
  refine ⟨main_totalSteps x y, ?_, ?_⟩
  · have hb := main_total_steps_bound x y
    rw [hx,hy] at hb
    have hq : main_totalSteps x y ≤ 32 * n^2 := by
      nlinarith
    exact_mod_cast hq
  · have hw := BinarySchoolbook.product_word_correct x y (by omega)
    rw [hx] at hw
    rw [← hw]
    exact halts_correct x y

end IntMul.TapeSchoolbook

namespace IntMul.TM

/-- A single fixed four-tape, five-symbol, nineteen-state machine computes
the exact padded product, with an explicit quadratic bound from n=1. -/
private theorem schoolbook : MulTimeBound fun n => (n : ℝ)^2 := by
  refine ⟨TapeSchoolbook.machine, ?_, (32 : ℝ), by norm_num, 1, ?_⟩
  · intro n hn
    exact ⟨32 * (n : ℝ)^2,TapeSchoolbook.multiplies_at n hn⟩
  · intro n _ hn
    exact TapeSchoolbook.multiplies_at n hn

end IntMul.TM


theorem solution : IntMul.MulTimeBound fun n => (n : ℝ)^2 :=
  IntMul.TM.schoolbook

#print axioms solution
