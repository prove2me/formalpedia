-- Prove2me | solution 1 for IntMul.TapeAdder.add_equal_width
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T18:39:01.525844+00:00
-- url     : https://prove2.me/submissions/ad44c2b8-aa49-4783-ab1a-53c641da5dbe

import Definitions.Def_IntMul_TapeAdder
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic


namespace IntMul.BinaryAdder

private theorem full_adder_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem add_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addLittle x y c).length = x.length + 1 := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => rfl
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, List.length_cons, ih ys _ ht]

private theorem add_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addLittle x y c) = littleVal x + littleVal y + c.toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [addLittle, littleVal]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, littleVal, ih ys _ ht]
          have hv := full_adder_value a b c
          omega

private theorem little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) a = 2 ^ x.length * a + IntMul.val x := by
  induction x generalizing a with
  | nil => simp [IntMul.val]
  | cons b xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hv : IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
        simp only [IntMul.val, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        exact ih b.toNat
      rw [hv, pow_succ]
      ring

private theorem val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact foldl_affine y _

private theorem val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, val_append, val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring

/-- Ripple-carry addition computes the ordinary campaign-model value, preserving
all leading zeroes and adding exactly one final carry position. -/
private theorem ripple_sum_spec (x y : List Bool) (h : x.length = y.length) :
    ((addLittle x.reverse y.reverse false).reverse).length = x.length + 1 ∧
    IntMul.val ((addLittle x.reverse y.reverse false).reverse) = IntMul.val x + IntMul.val y := by
  have hl : x.reverse.length = y.reverse.length := by simpa using h
  constructor
  · simpa using add_little_length x.reverse y.reverse false hl
  · rw [val_reverse_little, add_little_value _ _ _ hl]
    have hx : littleVal x.reverse = IntMul.val x := by
      rw [← val_reverse_little, List.reverse_reverse]
    have hy : littleVal y.reverse = IntMul.val y := by
      rw [← val_reverse_little, List.reverse_reverse]
    simp [hx, hy]

/-- Every little-endian word has exactly its specified binary digits, including
trailing zeroes; no normalization assumption is needed. -/
private theorem little_value_test_bit (x : List Bool) (i : ℕ) :
    (littleVal x).testBit i = x.getD i false := by
  induction x generalizing i with
  | nil => simp [littleVal]
  | cons b xs ih =>
      have hv : littleVal (b :: xs) = Nat.bit b (littleVal xs) := by
        cases b <;> simp [littleVal, Nat.bit] <;> omega
      rw [hv]
      cases i with
      | zero => cases b <;> simp [Nat.bit, Nat.testBit_zero]
      | succ i => rw [Nat.testBit_bit_succ]; simpa using ih i

/-- The campaign's padded big-endian binary encoding returns every original
word, preserving its declared width and any leading zeroes. -/
private theorem bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]

/-- The ripple adder produces exactly the canonical output word demanded by the
linear-time addition milestone, rather than merely a word of the same value. -/
private theorem ripple_sum_bin (x y : List Bool) (h : x.length = y.length) :
    (addLittle x.reverse y.reverse false).reverse =
      IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y) := by
  have hs := ripple_sum_spec x y h
  have hr := bin_value_roundtrip ((addLittle x.reverse y.reverse false).reverse)
  rw [hs.1, hs.2] at hr
  exact hr.symm

end IntMul.BinaryAdder




namespace IntMul.TapeAdder

open IntMul.TapeCopy (Sym)

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

private theorem initial_transition (a : Fin 3 → Sym) :
    transition .start a = (.copyX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, safe_right]

private theorem scan_bit_transition (a : Fin 3 → Sym)
    (hbit : a 0 = .zero ∨ a 0 = .one) :
    transition .scanY a = (.scanY, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  split <;> simp [safe_right, safe_stay]


private theorem tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private def copyFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyX
  cells := fun i => if i = 0 then
      machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
    else if i = 2 then machine.tapeOf ((x.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun _ => j + 1

private def scanFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .scanY
  cells := fun i => if i = 0 then
      machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
    else if i = 2 then machine.tapeOf (x.map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2 + j
    else if i = 2 then x.length else x.length + 1

private theorem copy_start (x y : List Bool) :
    machine.step (machine.initCfg x y) = copyFrame x y 0 := by
  have ht := initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
        0 Sym.start = machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
      exact Function.update_eq_self 0 _
    · change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
      exact Function.update_eq_self 0 _
    · change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
      exact Function.update_eq_self 0 _
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem copy_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (copyFrame x y j) = copyFrame x y (j + 1) := by
  have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
  have hinput : (copyFrame x y j).cells 0 ((copyFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hwork : (copyFrame x y j).cells 2 ((copyFrame x y j).head 2) = Sym.blank := by
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have hb : machine.bitSym x[j] = Sym.zero ∨ machine.bitSym x[j] = Sym.one := by
    cases h : x[j] <;> simp [MultitapeTM.bitSym, h]
  have ht : transition (copyFrame x y j).state
      (fun i => (copyFrame x y j).cells i ((copyFrame x y j).head i)) =
      (.copyX, fun i => (if i = 2 then machine.bitSym x[j]
        else (copyFrame x y j).cells i ((copyFrame x y j).head i), Move.right)) := by
    change transition .copyX _ = _
    simp only [transition, rawTransition, hinput, if_pos hb]
    congr 1
    funext i
    by_cases hi : i = 2
    · subst i
      simp only [if_pos rfl, hwork]
      cases h : x[j] <;> simp [safeStep, MultitapeTM.bitSym, h]
    · simp only [if_neg hi, safe_right]
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((copyFrame x y j).cells 0) ((copyFrame x y j).head 0)
        ((copyFrame x y j).cells 0 ((copyFrame x y j).head 0)) = (copyFrame x y j).cells 0
      exact Function.update_eq_self _ _
    · change Function.update (machine.tapeOf []) (j + 1) ((machine.tapeOf []) (j + 1)) = machine.tapeOf []
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

private theorem copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = copyFrame x y j := by
  induction j with
  | zero => simpa using copy_start x y
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), copy_step x y j (by omega)]


private theorem safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem copy_end_transition (a : Fin 3 → Sym) (hsep : a 0 = .sep)
    (hw : a 2 ≠ .start) : transition .copyX a =
      (.scanY, fun i => (a i, if i = 0 then .right else if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, hsep]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i <;> simp [safe_right, safe_stay, safe_left _ hw]

private theorem copy_end (x y : List Bool) :
    machine.step (copyFrame x y x.length) = scanFrame x y 0 := by
  have hsep : (copyFrame x y x.length).cells 0 ((copyFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : (copyFrame x y x.length).cells 2 ((copyFrame x y x.length).head 2) ≠ Sym.start := by
    change ((x.take x.length).map machine.bitSym).getD x.length machine.blank ≠ Sym.start
    rw [List.take_length, List.getD_eq_default _ _ (by simp)]
    decide
  have ht := copy_end_transition
    (fun i => (copyFrame x y x.length).cells i ((copyFrame x y x.length).head i)) hsep hw
  change transition (copyFrame x y x.length).state
    (fun i => (copyFrame x y x.length).cells i ((copyFrame x y x.length).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((copyFrame x y x.length).cells i) ((copyFrame x y x.length).head i)
      ((copyFrame x y x.length).cells i ((copyFrame x y x.length).head i)) = (scanFrame x y 0).cells i
    rw [Function.update_eq_self]
    fin_cases i <;> simp only [copyFrame, scanFrame, List.take_length]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [copyFrame, scanFrame]

private theorem scan_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (scanFrame x y j) = scanFrame x y (j + 1) := by
  have hinput : (scanFrame x y j).cells 0 ((scanFrame x y j).head 0) = machine.bitSym y[j] := by
    change (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
      (x.length + 2 + j) = _
    rw [show x.length + 2 + j = (x.length + 1 + j) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show x.length + 1 + j - x.length = j + 1 by omega,
      List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (scanFrame x y j).cells 0 ((scanFrame x y j).head 0) = Sym.zero ∨
      (scanFrame x y j).cells 0 ((scanFrame x y j).head 0) = Sym.one := by
    rw [hinput]
    cases y[j] <;> simp [MultitapeTM.bitSym]
  have ht := scan_bit_transition
    (fun i => (scanFrame x y j).cells i ((scanFrame x y j).head i)) hb
  change transition (scanFrame x y j).state
    (fun i => (scanFrame x y j).cells i ((scanFrame x y j).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((scanFrame x y j).cells i) ((scanFrame x y j).head i)
      ((scanFrame x y j).cells i ((scanFrame x y j).head i)) = (scanFrame x y (j + 1)).cells i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [scanFrame] <;> omega

private theorem scan_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (scanFrame x y 0) = scanFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), scan_step x y j (by omega)]


/-- A reverse-addition frame with unprocessed little-endian operands `xs,ys`,
fixed processed operand suffixes, and a completed output suffix. -/
private def rippleFrame (X xs ys dx dy out : List Bool) (c : Bool) : machine.Cfg where
  state := .add c
  cells := fun i => if i = 0 then
      machine.tapeOf (X.map machine.bitSym ++ machine.sep :: (ys.reverse ++ dy).map machine.bitSym)
    else if i = 2 then machine.tapeOf ((xs.reverse ++ dx).map machine.bitSym)
    else machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++ out.map machine.bitSym)
  head := fun i => if i = 0 then X.length + 1 + ys.length
    else if i = 2 then xs.length else xs.length + 1

private theorem reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem decode_bit (b : Bool) : decode (machine.bitSym b) = b := by
  cases b <;> decide

private theorem encode_bit (b : Bool) : encode b = machine.bitSym b := rfl

private theorem bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem add_bit_transition (a : Fin 3 → Sym) (x y c : Bool)
    (hx : a 2 = machine.bitSym x) (hy : a 0 = machine.bitSym y) (ho : a 1 = .blank) :
    transition (.add c) a = (.add (IntMul.BinaryAdder.carryBit x y c), fun i =>
      (if i = 1 then machine.bitSym (IntMul.BinaryAdder.sumBit x y c) else a i, .left)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (bit_ne_start x)]
  simp only [decode_bit, hy]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .left = (a 0, .left)
    rw [hy]
    exact safe_left _ (bit_ne_start y)
  · change safeStep (a 1) (machine.bitSym (IntMul.BinaryAdder.sumBit x y c)) .left =
      (machine.bitSym (IntMul.BinaryAdder.sumBit x y c), .left)
    rw [ho]
    cases IntMul.BinaryAdder.sumBit x y c <;> decide
  · change safeStep (a 2) (a 2) .left = (a 2, .left)
    rw [hx]
    exact safe_left _ (bit_ne_start x)

private theorem ripple_step (X xs ys dx dy out : List Bool) (a b c : Bool) :
    machine.step (rippleFrame X (a :: xs) (b :: ys) dx dy out c) =
      rippleFrame X xs ys (a :: dx) (b :: dy)
        (IntMul.BinaryAdder.sumBit a b c :: out) (IntMul.BinaryAdder.carryBit a b c) := by
  let f := rippleFrame X (a :: xs) (b :: ys) dx dy out c
  have hx : f.cells 2 (f.head 2) = machine.bitSym a := by
    change (machine.tapeOf (((a :: xs).reverse ++ dx).map machine.bitSym)) (xs.length + 1) = _
    simp only [MultitapeTM.tapeOf]
    exact reverse_last a xs dx
  have hy : f.cells 0 (f.head 0) = machine.bitSym b := by
    change (machine.tapeOf (X.map machine.bitSym ++ machine.sep :: ((b :: ys).reverse ++ dy).map machine.bitSym))
      (X.length + 1 + (ys.length + 1)) = _
    rw [show X.length + 1 + (ys.length + 1) = (X.length + 1 + ys.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show X.length + 1 + ys.length - X.length = ys.length + 1 by omega,
      List.getD_cons_succ]
    exact reverse_last b ys dy
  have ho : f.cells 1 (f.head 1) = Sym.blank := by
    change (List.replicate ((a :: xs).length + 1) Sym.blank ++ out.map machine.bitSym).getD
      (a :: xs).length machine.blank = Sym.blank
    rw [List.getD_append _ _ _ _ (by simp only [List.length_replicate]; omega)]
    exact List.getD_replicate Sym.blank (by omega)
  have ht := add_bit_transition (fun i => f.cells i (f.head i)) a b c hx hy ho
  change transition (rippleFrame X (a :: xs) (b :: ys) dx dy out c).state
    (fun i => (rippleFrame X (a :: xs) (b :: ys) dx dy out c).cells i
      ((rippleFrame X (a :: xs) (b :: ys) dx dy out c).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update (f.cells 0) (f.head 0) (f.cells 0 (f.head 0)) = _
      rw [Function.update_eq_self]
      simp [f, rippleFrame, List.reverse_cons, List.append_assoc]
    · change Function.update
        (machine.tapeOf (List.replicate (xs.length + 2) Sym.blank ++ out.map machine.bitSym))
        (xs.length + 2) (machine.bitSym (IntMul.BinaryAdder.sumBit a b c)) =
        machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++
          (IntMul.BinaryAdder.sumBit a b c :: out).map machine.bitSym)
      rw [show xs.length + 2 = (xs.length + 1) + 1 by omega,
        List.replicate_succ', List.append_assoc]
      simpa only [List.map_cons, List.length_replicate, List.singleton_append] using
        tape_replace_after_prefix machine (List.replicate (xs.length + 1) Sym.blank)
          (out.map machine.bitSym) Sym.blank (machine.bitSym (IntMul.BinaryAdder.sumBit a b c))
    · change Function.update (f.cells 2) (f.head 2) (f.cells 2 (f.head 2)) = _
      rw [Function.update_eq_self]
      simp [f, rippleFrame, List.reverse_cons, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [f, rippleFrame] <;> omega


private theorem add_end_transition (a : Fin 3 → Sym) (c : Bool)
    (hw : a 2 = .start) (ho : a 1 = .blank) :
    transition (.add c) a = (.halt, fun i =>
      (if i = 1 then machine.bitSym c else a i, .stay)) := by
  simp only [transition, rawTransition, hw, if_true]
  congr 1
  funext i
  by_cases hi : i = 1
  · subst i
    simp only [if_pos rfl, encode_bit]
    rw [ho]
    cases c <;> decide
  · simp only [if_neg hi, safe_stay]

private theorem ripple_stop (X dx dy out : List Bool) (c : Bool) :
    (machine.step (rippleFrame X [] [] dx dy out c)).state = .halt ∧
      (machine.step (rippleFrame X [] [] dx dy out c)).cells machine.outTape =
        machine.tapeOf ((c :: out).map machine.bitSym) := by
  have hw : (rippleFrame X [] [] dx dy out c).cells 2
      ((rippleFrame X [] [] dx dy out c).head 2) = Sym.start := rfl
  have ho : (rippleFrame X [] [] dx dy out c).cells 1
      ((rippleFrame X [] [] dx dy out c).head 1) = Sym.blank := rfl
  have ht := add_end_transition
    (fun i => (rippleFrame X [] [] dx dy out c).cells i
      ((rippleFrame X [] [] dx dy out c).head i)) c hw ho
  change transition (rippleFrame X [] [] dx dy out c).state
    (fun i => (rippleFrame X [] [] dx dy out c).cells i
      ((rippleFrame X [] [] dx dy out c).head i)) = _ at ht
  constructor
  · simp only [MultitapeTM.step, ht]
  · simp only [MultitapeTM.step, ht]
    change Function.update (machine.tapeOf (Sym.blank :: out.map machine.bitSym)) 1
      (machine.bitSym c) = machine.tapeOf ((c :: out).map machine.bitSym)
    simpa only [List.length_nil, List.nil_append, Nat.zero_add, List.map_cons] using
      tape_replace_after_prefix machine [] (out.map machine.bitSym) Sym.blank (machine.bitSym c)

private theorem ripple_run (X xs ys dx dy out : List Bool) (c : Bool)
    (h : xs.length = ys.length) :
    (machine.step^[xs.length + 1] (rippleFrame X xs ys dx dy out c)).state = .halt ∧
      (machine.step^[xs.length + 1] (rippleFrame X xs ys dx dy out c)).cells machine.outTape =
        machine.tapeOf (((IntMul.BinaryAdder.addLittle xs ys c).reverse ++ out).map machine.bitSym) := by
  induction xs generalizing ys dx dy out c with
  | nil =>
      cases ys with
      | nil => simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
          IntMul.BinaryAdder.addLittle, List.reverse_singleton, List.singleton_append] using
          ripple_stop X dx dy out c
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [show (a :: xs).length + 1 = (xs.length + 1) + 1 by simp,
            Function.iterate_succ_apply, ripple_step]
          simpa only [IntMul.BinaryAdder.addLittle, List.reverse_cons,
            List.append_assoc, List.singleton_append] using
            ih ys (a :: dx) (b :: dy) (IntMul.BinaryAdder.sumBit a b c :: out)
              (IntMul.BinaryAdder.carryBit a b c) ht

private theorem scan_end_transition (a : Fin 3 → Sym) (hb : a 0 = .blank) :
    transition .scanY a = (.add false, fun i => (a i, if i = 0 then .left else .stay)) := by
  simp only [transition, rawTransition, hb]
  rw [if_neg (by decide : ¬(Sym.blank = Sym.zero ∨ Sym.blank = Sym.one))]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    rw [hb]
    exact safe_left Sym.blank (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem blank_tape (n : ℕ) :
    machine.tapeOf (List.replicate n Sym.blank) = machine.tapeOf [] := by
  funext p
  cases p <;> simp [MultitapeTM.tapeOf, List.getD_eq_getElem?_getD]

private theorem scan_end (x y : List Bool) (h : x.length = y.length) :
    machine.step (scanFrame x y y.length) = rippleFrame x x.reverse y.reverse [] [] [] false := by
  have hb : (scanFrame x y y.length).cells 0 ((scanFrame x y y.length).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
      (x.length + 2 + y.length) = Sym.blank
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    exact List.getD_eq_default _ _ (by simp; omega)
  have ht := scan_end_transition
    (fun i => (scanFrame x y y.length).cells i ((scanFrame x y y.length).head i)) hb
  change transition (scanFrame x y y.length).state
    (fun i => (scanFrame x y y.length).cells i ((scanFrame x y y.length).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((scanFrame x y y.length).cells i) ((scanFrame x y y.length).head i)
      ((scanFrame x y y.length).cells i ((scanFrame x y y.length).head i)) =
        (rippleFrame x x.reverse y.reverse [] [] [] false).cells i
    rw [Function.update_eq_self]
    fin_cases i
    · simp [scanFrame, rippleFrame]
    · simp [scanFrame, rippleFrame]
      exact (blank_tape _).symm
    · simp [scanFrame, rippleFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [scanFrame, rippleFrame, h] <;> omega

/-- This fixed three-tape machine performs addition using exactly `3n+4`
actual transitions, with the canonical width-`n+1` output word. -/
theorem add_equal_width (x y : List Bool) (h : x.length = y.length) :
    machine.HaltsWithOutput x y (3 * x.length + 4)
      (IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y)) := by
  have hcopy : machine.step^[x.length + 2] (machine.initCfg x y) = scanFrame x y 0 := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply', copy_run x y x.length le_rfl, copy_end]
  have hscan : machine.step^[x.length + y.length + 3] (machine.initCfg x y) =
      rippleFrame x x.reverse y.reverse [] [] [] false := by
    rw [show x.length + y.length + 3 = (y.length + (x.length + 2)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hcopy,
      scan_run x y y.length le_rfl, scan_end x y h]
  have hr := ripple_run x x.reverse y.reverse [] [] [] false (by simpa using h)
  have hclock : 3 * x.length + 4 = (x.reverse.length + 1) + (x.length + y.length + 3) := by
    simp only [List.length_reverse]
    omega
  unfold MultitapeTM.HaltsWithOutput
  rw [hclock, Function.iterate_add_apply, hscan]
  simpa only [List.append_nil, IntMul.BinaryAdder.ripple_sum_bin x y h] using hr

/-- The addition half of the campaign's linear addition/subtraction milestone. -/
theorem add_linear : ∃ M : MultitapeTM, ∃ c : ℕ, 0 < c ∧
    ∀ x y : List Bool, x.length = y.length → ∃ t : ℕ,
      t ≤ c * (x.length + 1) ∧
        M.HaltsWithOutput x y t (IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y)) := by
  refine ⟨machine, 4, by decide, ?_⟩
  intro x y h
  exact ⟨3 * x.length + 4, by omega, add_equal_width x y h⟩

end IntMul.TapeAdder



theorem solution (x y : List Bool) (h : x.length = y.length) :
    IntMul.TapeAdder.machine.HaltsWithOutput x y (3 * x.length + 4)
      (IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y)) :=
  IntMul.TapeAdder.add_equal_width x y h

#print axioms solution
