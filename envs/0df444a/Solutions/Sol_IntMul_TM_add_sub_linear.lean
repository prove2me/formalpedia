-- Prove2me | solution 1 for IntMul.TM.add_sub_linear
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T18:50:06.506182+00:00
-- url     : https://prove2.me/submissions/ed6d5beb-a3bb-4496-83cc-ef7e52272dc1

import Definitions.Def_IntMul_TapeSubtractor
import Theorems.Thm_IntMul_TapeAdder_add_equal_width
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




namespace IntMul.BinarySubtractor

open IntMul.BinaryAdder

private theorem full_subtractor_value (a b c : Bool) :
    (diffBit a b c).toNat + b.toNat + c.toNat = a.toNat + 2 * (borrowBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem sub_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (subLittle x y c).length = x.length := by
  induction x generalizing y c with
  | nil => cases y <;> simp_all [subLittle]
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [subLittle, List.length_cons, ih ys _ ht]

/-- Exact value law including the final borrow, so no underflow is hidden. -/
private theorem sub_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (subLittle x y c) + littleVal y + c.toNat =
      littleVal x + 2 ^ x.length * (finalBorrow x y c).toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [subLittle, littleVal, finalBorrow]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          have hrest := ih ys (borrowBit a b c) ht
          have hbit := full_subtractor_value a b c
          simp only [subLittle, littleVal, finalBorrow, List.length_cons, pow_succ]
          nlinarith

private theorem sub_little_nonnegative (x y : List Bool) (c : Bool) (h : x.length = y.length)
    (hle : littleVal y + c.toNat ≤ littleVal x) :
    finalBorrow x y c = false ∧ littleVal (subLittle x y c) = littleVal x - (littleVal y + c.toNat) := by
  have hv := sub_little_value x y c h
  have hb := little_value_bound (subLittle x y c)
  rw [sub_little_length _ _ _ h] at hb
  cases he : finalBorrow x y c
  · simp only [he, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    exact ⟨rfl, by omega⟩
  · simp only [he, Bool.toNat_true, Nat.mul_one] at hv
    omega

/-- Canonical campaign output for subtraction without underflow. -/
private theorem ripple_difference_bin (x y : List Bool) (h : x.length = y.length)
    (hle : IntMul.val y ≤ IntMul.val x) :
    (subLittle x.reverse y.reverse false).reverse =
      IntMul.bin x.length (IntMul.val x - IntMul.val y) := by
  have hx : littleVal x.reverse = IntMul.val x := by rw [← val_reverse_little, List.reverse_reverse]
  have hy : littleVal y.reverse = IntMul.val y := by rw [← val_reverse_little, List.reverse_reverse]
  have he : x.reverse.length = y.reverse.length := by simpa using h
  have hv := (sub_little_nonnegative x.reverse y.reverse false he (by simpa [hx, hy] using hle)).2
  rw [hx, hy] at hv
  have hl : (subLittle x.reverse y.reverse false).reverse.length = x.length := by
    simpa using sub_little_length x.reverse y.reverse false he
  have hval : IntMul.val (subLittle x.reverse y.reverse false).reverse = IntMul.val x - IntMul.val y := by
    simpa [val_reverse_little] using hv
  have hr := bin_value_roundtrip (subLittle x.reverse y.reverse false).reverse
  rw [hl, hval] at hr
  exact hr.symm

private theorem val_cons (b : Bool) (xs : List Bool) :
    IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
  change IntMul.val ([b] ++ xs) = _
  rw [val_append, val_singleton]

private theorem val_bound (x : List Bool) : IntMul.val x < 2 ^ x.length := by
  have hv := little_value_bound x.reverse
  rw [← val_reverse_little, List.reverse_reverse, List.length_reverse] at hv
  exact hv

private theorem compare_absorbing (x y : List Bool) (h : x.length = y.length) :
    compareWords x y .lt = .lt ∧ compareWords x y .gt = .gt := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [compareWords]
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simpa only [compareWords, compareStep] using ih ys ht

/-- The finite-state comparison scan agrees with numeric comparison on every
fixed-width big-endian word, with leading zeroes retained. -/
private theorem compare_correct (x y : List Bool) (h : x.length = y.length) :
    compareWords x y .eq = (if IntMul.val x < IntMul.val y then .lt
      else if IntMul.val y < IntMul.val x then .gt else .eq) := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [compareWords, IntMul.val]
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          have hbX := val_bound xs
          have hbY := val_bound ys
          have hl := (compare_absorbing xs ys ht).1
          have hg := (compare_absorbing xs ys ht).2
          cases a <;> cases b
          · simpa [compareWords, compareStep, val_cons] using ih ys ht
          · simp only [compareWords, compareStep, Bool.false_eq_true, if_false,
              if_true, hl, val_cons, Bool.toNat_false, Bool.toNat_true,
              Nat.mul_zero, Nat.zero_add, Nat.mul_one]
            rw [← ht] at hbY ⊢
            rw [if_pos (by omega)]
          · simp only [compareWords, compareStep, Bool.true_eq_false, if_false,
              Bool.false_eq_true, if_false, hg, val_cons, Bool.toNat_false, Bool.toNat_true,
              Nat.mul_zero, Nat.zero_add, Nat.mul_one]
            rw [← ht] at hbY
            rw [if_neg (by omega), if_pos (by omega)]
          · simpa [compareWords, compareStep, val_cons, ht] using ih ys ht

end IntMul.BinarySubtractor



namespace IntMul.TapeSubtractor

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay encode decode)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
theorem tape_replace_after_prefix (M : MultitapeTM)
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

theorem safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

theorem tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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
    else if i = 2 ∨ i = 3 then machine.tapeOf ((x.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun _ => j + 1

private def rewindFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .rewind
  cells := fun i => if i = 0 then
      machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (x.map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2
    else if i = 2 then x.length else if i = 3 then j else x.length + 1

private theorem initial_transition (a : Fin 4 → Sym) :
    transition .start a = (.copyX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, safe_right]

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
    all_goals
      change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
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
  have hwork : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (copyFrame x y j).cells i ((copyFrame x y j).head i) = Sym.blank := by
    intro i hi
    change (if i = 0 then machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
      else if i = 2 ∨ i = 3 then machine.tapeOf ((x.take j).map machine.bitSym)
      else machine.tapeOf []) (j + 1) = Sym.blank
    have hn : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    rw [if_neg hn, if_pos hi]
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have hb : machine.bitSym x[j] = Sym.zero ∨ machine.bitSym x[j] = Sym.one := by
    cases x[j] <;> simp [MultitapeTM.bitSym]
  have ht : transition (copyFrame x y j).state
      (fun i => (copyFrame x y j).cells i ((copyFrame x y j).head i)) =
      (.copyX, fun i => (if i = 2 ∨ i = 3 then machine.bitSym x[j]
        else (copyFrame x y j).cells i ((copyFrame x y j).head i), Move.right)) := by
    change transition .copyX _ = _
    simp only [transition, rawTransition, hinput, if_pos hb]
    congr 1
    funext i
    by_cases hi : i = 2 ∨ i = 3
    · simp only [if_pos hi, hwork i hi]
      cases x[j] <;> simp [safeStep, MultitapeTM.bitSym]
    · simp only [if_neg hi, safe_right]
  have hnew : (x.take (j + 1)).map machine.bitSym =
      (x.take j).map machine.bitSym ++ [machine.bitSym x[j]] := by
    rw [List.take_succ_eq_append_getElem hj, List.map_append]
    rfl
  have hwrite := tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
  rw [hl] at hwrite
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
    all_goals
      change Function.update (machine.tapeOf ((x.take j).map machine.bitSym)) (j + 1)
        (machine.bitSym x[j]) = machine.tapeOf ((x.take (j + 1)).map machine.bitSym)
      rw [hnew]
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

private theorem copy_end_transition (a : Fin 4 → Sym) (hsep : a 0 = .sep)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i ≠ .start) : transition .copyX a =
      (.rewind, fun i => (a i, if i = 0 then .right else if i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hsep]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [safe_right]
  · simp only [if_neg h0]
    by_cases hi : i = 2 ∨ i = 3
    · simp only [if_pos hi]
      exact safe_left _ (hw i hi)
    · simp only [if_neg hi, safe_stay]

private theorem copy_end (x y : List Bool) :
    machine.step (copyFrame x y x.length) = rewindFrame x y x.length := by
  have hsep : (copyFrame x y x.length).cells 0 ((copyFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (copyFrame x y x.length).cells i ((copyFrame x y x.length).head i) ≠ Sym.start := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    change (if i = 0 then machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
      else if i = 2 ∨ i = 3 then machine.tapeOf ((x.take x.length).map machine.bitSym)
      else machine.tapeOf []) (x.length + 1) ≠ Sym.start
    rw [if_neg h0, if_pos hi]
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
      ((copyFrame x y x.length).cells i ((copyFrame x y x.length).head i)) = (rewindFrame x y x.length).cells i
    rw [Function.update_eq_self]
    fin_cases i <;> simp only [copyFrame, rewindFrame, List.take_length]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [copyFrame, rewindFrame]

private theorem rewind_left_transition (a : Fin 4 → Sym) (h : a 3 ≠ .start) :
    transition .rewind a = (.rewind, fun i => (a i, if i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, if_neg h]
  congr 1
  funext i
  by_cases hi : i = 3
  · subst i
    simp only [if_pos rfl]
    exact safe_left _ h
  · simp only [if_neg hi, safe_stay]

private theorem rewind_step (x y : List Bool) (j : ℕ) (hj : j + 1 ≤ x.length) :
    machine.step (rewindFrame x y (j + 1)) = rewindFrame x y j := by
  have hread : (rewindFrame x y (j + 1)).cells 3 ((rewindFrame x y (j + 1)).head 3) = machine.bitSym x[j] := by
    change (x.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  have hn : (rewindFrame x y (j + 1)).cells 3 ((rewindFrame x y (j + 1)).head 3) ≠ Sym.start := by
    rw [hread]
    cases x[j] <;> decide
  have ht := rewind_left_transition
    (fun i => (rewindFrame x y (j + 1)).cells i ((rewindFrame x y (j + 1)).head i)) hn
  change transition (rewindFrame x y (j + 1)).state
    (fun i => (rewindFrame x y (j + 1)).cells i ((rewindFrame x y (j + 1)).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame x y (j + 1)).cells i) ((rewindFrame x y (j + 1)).head i)
      ((rewindFrame x y (j + 1)).cells i ((rewindFrame x y (j + 1)).head i)) = (rewindFrame x y j).cells i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [rewindFrame]

private theorem rewind_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j] (rewindFrame x y j) = rewindFrame x y 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply, rewind_step x y j hj, ih (by omega)]


private def compareFrame (X xs ys dx dy : List Bool) (q : IntMul.BinarySubtractor.Comparison) : machine.Cfg where
  state := .compare q
  cells := fun i => if i = 0 then
      machine.tapeOf (X.map machine.bitSym ++ machine.sep :: (dy ++ ys).map machine.bitSym)
    else if i = 2 then machine.tapeOf (X.map machine.bitSym)
    else if i = 3 then machine.tapeOf ((dx ++ xs).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then X.length + 2 + dy.length
    else if i = 2 then X.length else if i = 3 then dx.length + 1 else X.length + 1

private theorem rewind_end_transition (a : Fin 4 → Sym) (h : a 3 = .start) :
    transition .rewind a = (.compare .eq, fun i => (a i, if i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 3
  · simp only [if_pos hi, safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem rewind_end (x y : List Bool) :
    machine.step (rewindFrame x y 0) = compareFrame x x y [] [] .eq := by
  have hm : (rewindFrame x y 0).cells 3 ((rewindFrame x y 0).head 3) = Sym.start := rfl
  have ht := rewind_end_transition
    (fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)) hm
  change transition (rewindFrame x y 0).state
    (fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame x y 0).cells i) ((rewindFrame x y 0).head i)
      ((rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)) = (compareFrame x x y [] [] .eq).cells i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [rewindFrame, compareFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [rewindFrame, compareFrame]

private theorem decode_bit (b : Bool) : decode (machine.bitSym b) = b := by
  cases b <;> decide

private theorem compare_bit_transition (a : Fin 4 → Sym)
    (x y : Bool) (q : IntMul.BinarySubtractor.Comparison)
    (hx : a 3 = machine.bitSym x) (hy : a 0 = machine.bitSym y) :
    transition (.compare q) a = (.compare (IntMul.BinarySubtractor.compareStep q x y),
      fun i => (a i, if i = 0 ∨ i = 3 then .right else .stay)) := by
  have hb : a 0 = Sym.zero ∨ a 0 = Sym.one := by
    rw [hy]
    cases y <;> simp [MultitapeTM.bitSym]
  simp only [transition, rawTransition, if_pos hb]
  simp only [hx, hy, decode_bit]
  congr 1
  funext i
  by_cases hi : i = 0 ∨ i = 3
  · simp only [if_pos hi, safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem compare_step (X xs ys dx dy : List Bool) (a b : Bool)
    (q : IntMul.BinarySubtractor.Comparison) :
    machine.step (compareFrame X (a :: xs) (b :: ys) dx dy q) =
      compareFrame X xs ys (dx ++ [a]) (dy ++ [b]) (IntMul.BinarySubtractor.compareStep q a b) := by
  have hx : (compareFrame X (a :: xs) (b :: ys) dx dy q).cells 3
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).head 3) = machine.bitSym a := by
    change ((dx ++ a :: xs).map machine.bitSym).getD dx.length machine.blank = _
    rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hy : (compareFrame X (a :: xs) (b :: ys) dx dy q).cells 0
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).head 0) = machine.bitSym b := by
    change (machine.tapeOf (X.map machine.bitSym ++ machine.sep :: (dy ++ b :: ys).map machine.bitSym))
      (X.length + 2 + dy.length) = _
    rw [show X.length + 2 + dy.length = (X.length + 1 + dy.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show X.length + 1 + dy.length - X.length = dy.length + 1 by omega,
      List.getD_cons_succ]
    rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := compare_bit_transition
    (fun i => (compareFrame X (a :: xs) (b :: ys) dx dy q).cells i
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).head i)) a b q hx hy
  change transition (compareFrame X (a :: xs) (b :: ys) dx dy q).state
    (fun i => (compareFrame X (a :: xs) (b :: ys) dx dy q).cells i
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((compareFrame X (a :: xs) (b :: ys) dx dy q).cells i)
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).head i)
      ((compareFrame X (a :: xs) (b :: ys) dx dy q).cells i
        ((compareFrame X (a :: xs) (b :: ys) dx dy q).head i)) =
          (compareFrame X xs ys (dx ++ [a]) (dy ++ [b]) (IntMul.BinarySubtractor.compareStep q a b)).cells i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [compareFrame, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [compareFrame] <;> omega

private theorem compare_run (X xs ys dx dy : List Bool) (q : IntMul.BinarySubtractor.Comparison)
    (h : xs.length = ys.length) :
    machine.step^[xs.length] (compareFrame X xs ys dx dy q) =
      compareFrame X [] [] (dx ++ xs) (dy ++ ys) (IntMul.BinarySubtractor.compareWords xs ys q) := by
  induction xs generalizing ys dx dy q with
  | nil =>
      cases ys with
      | nil => simp [IntMul.BinarySubtractor.compareWords]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [List.length_cons, Function.iterate_succ_apply, compare_step]
          simpa only [IntMul.BinarySubtractor.compareWords, List.append_assoc, List.singleton_append] using
            ih ys (dx ++ [a]) (dy ++ [b]) (IntMul.BinarySubtractor.compareStep q a b) ht


private def borrowFrame (X xs ys dx dy out : List Bool) (s c : Bool) : machine.Cfg where
  state := .sub s c
  cells := fun i => if i = 0 then
      machine.tapeOf (X.map machine.bitSym ++ machine.sep :: (ys.reverse ++ dy).map machine.bitSym)
    else if i = 2 then machine.tapeOf ((xs.reverse ++ dx).map machine.bitSym)
    else if i = 3 then machine.tapeOf (X.map machine.bitSym)
    else machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++ out.map machine.bitSym)
  head := fun i => if i = 0 then X.length + 1 + ys.length
    else if i = 2 then xs.length else if i = 3 then X.length + 1 else xs.length + 1
private theorem reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp


private theorem encode_bit (b : Bool) : encode b = machine.bitSym b := rfl

private theorem bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem sub_bit_transition (a : Fin 4 → Sym) (x y s c : Bool)
    (hx : a 2 = machine.bitSym x) (hy : a 0 = machine.bitSym y) (ho : a 1 = .blank) :
    transition (.sub s c) a =
      (.sub s (IntMul.BinarySubtractor.borrowBit (if s then y else x) (if s then x else y) c),
        fun i => (if i = 1 then machine.bitSym
          (IntMul.BinarySubtractor.diffBit (if s then y else x) (if s then x else y) c)
          else a i, if i = 3 then .stay else .left)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (bit_ne_start x)]
  simp only [hy, decode_bit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .left = (a 0, .left)
    rw [hy]
    exact safe_left _ (bit_ne_start y)
  · change safeStep (a 1) (machine.bitSym
      (IntMul.BinarySubtractor.diffBit (if s then y else x) (if s then x else y) c)) .left =
        (machine.bitSym (IntMul.BinarySubtractor.diffBit (if s then y else x) (if s then x else y) c), .left)
    rw [ho]
    cases IntMul.BinarySubtractor.diffBit (if s then y else x) (if s then x else y) c <;> decide
  · change safeStep (a 2) (a 2) .left = (a 2, .left)
    rw [hx]
    exact safe_left _ (bit_ne_start x)
  · change safeStep (a 3) (a 3) .stay = (a 3, .stay)
    exact safe_stay _

private theorem borrow_step (X xs ys dx dy out : List Bool) (a b s c : Bool) :
    machine.step (borrowFrame X (a :: xs) (b :: ys) dx dy out s c) =
      borrowFrame X xs ys (a :: dx) (b :: dy)
        (IntMul.BinarySubtractor.diffBit (if s then b else a) (if s then a else b) c :: out)
          s (IntMul.BinarySubtractor.borrowBit (if s then b else a) (if s then a else b) c) := by
  let f := borrowFrame X (a :: xs) (b :: ys) dx dy out s c
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
  have ht := sub_bit_transition (fun i => f.cells i (f.head i)) a b s c hx hy ho
  change transition (borrowFrame X (a :: xs) (b :: ys) dx dy out s c).state
    (fun i => (borrowFrame X (a :: xs) (b :: ys) dx dy out s c).cells i
      ((borrowFrame X (a :: xs) (b :: ys) dx dy out s c).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update (f.cells 0) (f.head 0) (f.cells 0 (f.head 0)) = _
      rw [Function.update_eq_self]
      simp [f, borrowFrame, List.reverse_cons, List.append_assoc]
    · change Function.update
        (machine.tapeOf (List.replicate (xs.length + 2) Sym.blank ++ out.map machine.bitSym))
        (xs.length + 2) (machine.bitSym (IntMul.BinarySubtractor.diffBit (if s then b else a) (if s then a else b) c)) =
        machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++
          (IntMul.BinarySubtractor.diffBit (if s then b else a) (if s then a else b) c :: out).map machine.bitSym)
      rw [show xs.length + 2 = (xs.length + 1) + 1 by omega,
        List.replicate_succ', List.append_assoc]
      simpa only [List.map_cons, List.length_replicate, List.singleton_append] using
        tape_replace_after_prefix machine (List.replicate (xs.length + 1) Sym.blank)
          (out.map machine.bitSym) Sym.blank
            (machine.bitSym (IntMul.BinarySubtractor.diffBit (if s then b else a) (if s then a else b) c))
    · change Function.update (f.cells 2) (f.head 2) (f.cells 2 (f.head 2)) = _
      rw [Function.update_eq_self]
      simp [f, borrowFrame, List.reverse_cons, List.append_assoc]
    · change Function.update (f.cells 3) (f.head 3) (f.cells 3 (f.head 3)) = _
      rw [Function.update_eq_self]
      simp [f, borrowFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [borrowFrame]


private theorem sub_end_transition (a : Fin 4 → Sym) (s c : Bool)
    (hw : a 2 = .start) (ho : a 1 = .blank) :
    transition (.sub s c) a = (.halt, fun i =>
      (if i = 1 then machine.bitSym s else a i, .stay)) := by
  simp only [transition, rawTransition, hw, if_true]
  congr 1
  funext i
  by_cases hi : i = 1
  · subst i
    simp only [if_pos rfl, encode_bit]
    rw [ho]
    cases s <;> decide
  · simp only [if_neg hi, safe_stay]

private theorem borrow_stop (X dx dy out : List Bool) (s c : Bool) :
    (machine.step (borrowFrame X [] [] dx dy out s c)).state = .halt ∧
      (machine.step (borrowFrame X [] [] dx dy out s c)).cells machine.outTape =
        machine.tapeOf ((s :: out).map machine.bitSym) := by
  have hw : (borrowFrame X [] [] dx dy out s c).cells 2
      ((borrowFrame X [] [] dx dy out s c).head 2) = Sym.start := rfl
  have ho : (borrowFrame X [] [] dx dy out s c).cells 1
      ((borrowFrame X [] [] dx dy out s c).head 1) = Sym.blank := rfl
  have ht := sub_end_transition
    (fun i => (borrowFrame X [] [] dx dy out s c).cells i
      ((borrowFrame X [] [] dx dy out s c).head i)) s c hw ho
  change transition (borrowFrame X [] [] dx dy out s c).state
    (fun i => (borrowFrame X [] [] dx dy out s c).cells i
      ((borrowFrame X [] [] dx dy out s c).head i)) = _ at ht
  constructor
  · simp only [MultitapeTM.step, ht]
  · simp only [MultitapeTM.step, ht]
    change Function.update (machine.tapeOf (Sym.blank :: out.map machine.bitSym)) 1
      (machine.bitSym s) = machine.tapeOf ((s :: out).map machine.bitSym)
    simpa only [List.length_nil, List.nil_append, Nat.zero_add, List.map_cons] using
      tape_replace_after_prefix machine [] (out.map machine.bitSym) Sym.blank (machine.bitSym s)

private theorem borrow_run (X xs ys dx dy out : List Bool) (s c : Bool)
    (h : xs.length = ys.length) :
    (machine.step^[xs.length + 1] (borrowFrame X xs ys dx dy out s c)).state = .halt ∧
      (machine.step^[xs.length + 1] (borrowFrame X xs ys dx dy out s c)).cells machine.outTape =
        machine.tapeOf ((s :: ((if s then IntMul.BinarySubtractor.subLittle ys xs c
          else IntMul.BinarySubtractor.subLittle xs ys c).reverse ++ out)).map machine.bitSym) := by
  induction xs generalizing ys dx dy out c with
  | nil =>
      cases ys with
      | nil => simpa [IntMul.BinarySubtractor.subLittle] using borrow_stop X dx dy out s c
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [show (a :: xs).length + 1 = (xs.length + 1) + 1 by simp,
            Function.iterate_succ_apply, borrow_step]
          have hr := ih ys (a :: dx) (b :: dy)
            (IntMul.BinarySubtractor.diffBit (if s then b else a) (if s then a else b) c :: out)
              (IntMul.BinarySubtractor.borrowBit (if s then b else a) (if s then a else b) c) ht
          cases s <;> simpa only [Bool.false_eq_true, if_false, if_true,
            IntMul.BinarySubtractor.subLittle, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hr

private theorem compare_end_transition (a : Fin 4 → Sym)
    (q : IntMul.BinarySubtractor.Comparison) (hb : a 0 = .blank) :
    transition (.compare q) a = (.sub (q == .lt) false,
      fun i => (a i, if i = 0 then .left else .stay)) := by
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

private theorem compare_end (x y : List Bool) (q : IntMul.BinarySubtractor.Comparison) :
    machine.step (compareFrame x [] [] x y q) =
      borrowFrame x x.reverse y.reverse [] [] [] (q == .lt) false := by
  have hb : (compareFrame x [] [] x y q).cells 0 ((compareFrame x [] [] x y q).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: (y ++ []).map machine.bitSym))
      (x.length + 2 + y.length) = Sym.blank
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.append_nil]
    exact List.getD_eq_default _ _ (by simp; omega)
  have ht := compare_end_transition
    (fun i => (compareFrame x [] [] x y q).cells i ((compareFrame x [] [] x y q).head i)) q hb
  change transition (compareFrame x [] [] x y q).state
    (fun i => (compareFrame x [] [] x y q).cells i ((compareFrame x [] [] x y q).head i)) = _ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((compareFrame x [] [] x y q).cells i) ((compareFrame x [] [] x y q).head i)
      ((compareFrame x [] [] x y q).cells i ((compareFrame x [] [] x y q).head i)) =
        (borrowFrame x x.reverse y.reverse [] [] [] (q == .lt) false).cells i
    rw [Function.update_eq_self]
    fin_cases i
    · simp [compareFrame, borrowFrame]
    · simp [compareFrame, borrowFrame]
      exact (blank_tape _).symm
    · simp [compareFrame, borrowFrame]
    · simp [compareFrame, borrowFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [compareFrame, borrowFrame]

private theorem comparison_sign (x y : List Bool) (h : x.length = y.length) :
    (IntMul.BinarySubtractor.compareWords x y .eq == .lt) = decide (IntMul.val x < IntMul.val y) := by
  rw [IntMul.BinarySubtractor.compare_correct x y h]
  by_cases hl : IntMul.val x < IntMul.val y
  · simp only [if_pos hl, decide_eq_true hl]
    rfl
  · simp only [if_neg hl, decide_eq_false hl]
    split_ifs <;> rfl

private theorem signed_ripple_bin (x y : List Bool) (h : x.length = y.length) :
    let s := IntMul.BinarySubtractor.compareWords x y .eq == .lt
    s :: (if s then IntMul.BinarySubtractor.subLittle y.reverse x.reverse false
      else IntMul.BinarySubtractor.subLittle x.reverse y.reverse false).reverse =
        decide (IntMul.val x < IntMul.val y) ::
          IntMul.bin x.length (if IntMul.val y ≤ IntMul.val x then IntMul.val x - IntMul.val y
            else IntMul.val y - IntMul.val x) := by
  simp only [comparison_sign x y h]
  by_cases hlt : IntMul.val x < IntMul.val y
  · simp only [decide_eq_true hlt, if_true, if_neg (by omega : ¬IntMul.val y ≤ IntMul.val x)]
    rw [IntMul.BinarySubtractor.ripple_difference_bin y x h.symm (by omega), h]
  · simp only [decide_eq_false hlt, Bool.false_eq_true, if_false,
      if_pos (by omega : IntMul.val y ≤ IntMul.val x)]
    rw [IntMul.BinarySubtractor.ripple_difference_bin x y h (by omega)]

/-- A single fixed four-tape machine computes signed absolute subtraction in
`4n+5` literal transitions for every pair of equal-width words. -/
theorem sub_equal_width (x y : List Bool) (h : x.length = y.length) :
    machine.HaltsWithOutput x y (4 * x.length + 5)
      (decide (IntMul.val x < IntMul.val y) ::
        IntMul.bin x.length (if IntMul.val y ≤ IntMul.val x then IntMul.val x - IntMul.val y
          else IntMul.val y - IntMul.val x)) := by
  have hcopy : machine.step^[x.length + 2] (machine.initCfg x y) = rewindFrame x y x.length := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply', copy_run x y x.length le_rfl, copy_end]
  have hrewind : machine.step^[2 * x.length + 3] (machine.initCfg x y) = compareFrame x x y [] [] .eq := by
    rw [show 2 * x.length + 3 = (x.length + (x.length + 2)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hcopy,
      rewind_run x y x.length le_rfl, rewind_end]
  have hcompare : machine.step^[3 * x.length + 4] (machine.initCfg x y) =
      borrowFrame x x.reverse y.reverse [] [] [] (IntMul.BinarySubtractor.compareWords x y .eq == .lt) false := by
    rw [show 3 * x.length + 4 = (x.length + (2 * x.length + 3)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hrewind,
      compare_run x x y [] [] .eq h]
    simp only [List.nil_append, compare_end]
  have hr := borrow_run x x.reverse y.reverse [] [] []
    (IntMul.BinarySubtractor.compareWords x y .eq == .lt) false (by simpa using h)
  have hclock : 4 * x.length + 5 = (x.reverse.length + 1) + (3 * x.length + 4) := by
    simp only [List.length_reverse]
    omega
  unfold MultitapeTM.HaltsWithOutput
  rw [hclock, Function.iterate_add_apply, hcompare]
  simpa only [List.append_nil, signed_ripple_bin x y h] using hr

end IntMul.TapeSubtractor



open IntMul

theorem solution :
    (∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ x y : List Bool, x.length = y.length →
      ∃ t : ℕ, (t : ℝ) ≤ c * (x.length + 1) ∧
        M.HaltsWithOutput x y t (bin (x.length + 1) (val x + val y))) ∧
    (∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ x y : List Bool, x.length = y.length →
      ∃ t : ℕ, (t : ℝ) ≤ c * (x.length + 1) ∧
        M.HaltsWithOutput x y t
          (decide (val x < val y) ::
            bin x.length (if val y ≤ val x then val x - val y else val y - val x)))  := by
  constructor
  · refine ⟨IntMul.TapeAdder.machine, (4 : ℝ), by norm_num, ?_⟩
    intro x y h
    refine ⟨3 * x.length + 4, ?_, IntMul.TapeAdder.add_equal_width x y h⟩
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) x.length]
  · refine ⟨IntMul.TapeSubtractor.machine, (5 : ℝ), by norm_num, ?_⟩
    intro x y h
    refine ⟨4 * x.length + 5, ?_, IntMul.TapeSubtractor.sub_equal_width x y h⟩
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) x.length]

#print axioms solution
