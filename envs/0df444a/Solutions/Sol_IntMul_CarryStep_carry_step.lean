-- Prove2me | solution 1 for IntMul.CarryStep.carry_step
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T10:10:29.01928+00:00
-- url     : https://prove2.me/submissions/b0bb8cd4-e1cf-49e0-93f4-6fd3a63d824f

import Definitions.Def_IntMul_CarryStep
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_TapeAdder
import Mathlib.Data.List.GetD
import Definitions.Def_IntMul_CountedStream
import Definitions.Def_IntMul_CountedStreamFrames
import Mathlib.Data.List.TakeDrop
import Theorems.Thm_IntMul_FiniteCaller_simulate_run



namespace IntMul.BinaryAdder

private theorem owned_intmulcarrystepadder_full_adder_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem owned_intmulcarrystepadder_add_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
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

private theorem owned_intmulcarrystepadder_add_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
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
          have hv := owned_intmulcarrystepadder_full_adder_value a b c
          omega

private theorem owned_intmulcarrystepadder_little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem owned_intmulcarrystepadder_foldl_affine (x : List Bool) (a : ℕ) :
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

private theorem owned_intmulcarrystepadder_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact owned_intmulcarrystepadder_foldl_affine y _

private theorem owned_intmulcarrystepadder_val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem owned_intmulcarrystepadder_val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, owned_intmulcarrystepadder_val_append, owned_intmulcarrystepadder_val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring

/-- Ripple-carry addition computes the ordinary campaign-model value, preserving
all leading zeroes and adding exactly one final carry position. -/
private theorem owned_intmulcarrystepadder_ripple_sum_spec (x y : List Bool) (h : x.length = y.length) :
    ((addLittle x.reverse y.reverse false).reverse).length = x.length + 1 ∧
    IntMul.val ((addLittle x.reverse y.reverse false).reverse) = IntMul.val x + IntMul.val y := by
  have hl : x.reverse.length = y.reverse.length := by simpa using h
  constructor
  · simpa using owned_intmulcarrystepadder_add_little_length x.reverse y.reverse false hl
  · rw [owned_intmulcarrystepadder_val_reverse_little, owned_intmulcarrystepadder_add_little_value _ _ _ hl]
    have hx : littleVal x.reverse = IntMul.val x := by
      rw [← owned_intmulcarrystepadder_val_reverse_little, List.reverse_reverse]
    have hy : littleVal y.reverse = IntMul.val y := by
      rw [← owned_intmulcarrystepadder_val_reverse_little, List.reverse_reverse]
    simp [hx, hy]

/-- Every little-endian word has exactly its specified binary digits, including
trailing zeroes; no normalization assumption is needed. -/
private theorem owned_intmulcarrystepadder_little_value_test_bit (x : List Bool) (i : ℕ) :
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
private theorem owned_intmulcarrystepadder_bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← owned_intmulcarrystepadder_val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, owned_intmulcarrystepadder_little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]

/-- The ripple adder produces exactly the canonical output word demanded by the
linear-time addition milestone, rather than merely a word of the same value. -/
private theorem owned_intmulcarrystepadder_ripple_sum_bin (x y : List Bool) (h : x.length = y.length) :
    (addLittle x.reverse y.reverse false).reverse =
      IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y) := by
  have hs := owned_intmulcarrystepadder_ripple_sum_spec x y h
  have hr := owned_intmulcarrystepadder_bin_value_roundtrip ((addLittle x.reverse y.reverse false).reverse)
  rw [hs.1, hs.2] at hr
  exact hr.symm

end IntMul.BinaryAdder




namespace IntMul.TapeAdder

open IntMul.TapeCopy (Sym)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem owned_intmulcarrystepadder_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem owned_intmulcarrystepadder_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcarrystepadder_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcarrystepadder_initial_transition (a : Fin 3 → Sym) :
    transition .start a = (.copyX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, owned_intmulcarrystepadder_safe_right]

private theorem owned_intmulcarrystepadder_scan_bit_transition (a : Fin 3 → Sym)
    (hbit : a 0 = .zero ∨ a 0 = .one) :
    transition .scanY a = (.scanY, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  split <;> simp [owned_intmulcarrystepadder_safe_right, safe_stay]


private theorem owned_intmulcarrystepadder_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private def owned_intmulcarrystepadder_copyFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyX
  cells := fun i => if i = 0 then
      machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
    else if i = 2 then machine.tapeOf ((x.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun _ => j + 1

private def owned_intmulcarrystepadder_scanFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .scanY
  cells := fun i => if i = 0 then
      machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
    else if i = 2 then machine.tapeOf (x.map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2 + j
    else if i = 2 then x.length else x.length + 1

private theorem owned_intmulcarrystepadder_copy_start (x y : List Bool) :
    machine.step (machine.initCfg x y) = owned_intmulcarrystepadder_copyFrame x y 0 := by
  have ht := owned_intmulcarrystepadder_initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply owned_intmulcarrystepadder_cfg_ext
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

private theorem owned_intmulcarrystepadder_copy_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (owned_intmulcarrystepadder_copyFrame x y j) = owned_intmulcarrystepadder_copyFrame x y (j + 1) := by
  have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
  have hinput : (owned_intmulcarrystepadder_copyFrame x y j).cells 0 ((owned_intmulcarrystepadder_copyFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hwork : (owned_intmulcarrystepadder_copyFrame x y j).cells 2 ((owned_intmulcarrystepadder_copyFrame x y j).head 2) = Sym.blank := by
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have hb : machine.bitSym x[j] = Sym.zero ∨ machine.bitSym x[j] = Sym.one := by
    cases h : x[j] <;> simp [MultitapeTM.bitSym, h]
  have ht : transition (owned_intmulcarrystepadder_copyFrame x y j).state
      (fun i => (owned_intmulcarrystepadder_copyFrame x y j).cells i ((owned_intmulcarrystepadder_copyFrame x y j).head i)) =
      (.copyX, fun i => (if i = 2 then machine.bitSym x[j]
        else (owned_intmulcarrystepadder_copyFrame x y j).cells i ((owned_intmulcarrystepadder_copyFrame x y j).head i), Move.right)) := by
    change transition .copyX _ = _
    simp only [transition, rawTransition, hinput, if_pos hb]
    congr 1
    funext i
    by_cases hi : i = 2
    · subst i
      simp only [if_pos rfl, hwork]
      cases h : x[j] <;> simp [safeStep, MultitapeTM.bitSym, h]
    · simp only [if_neg hi, owned_intmulcarrystepadder_safe_right]
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcarrystepadder_copyFrame x y j).cells 0) ((owned_intmulcarrystepadder_copyFrame x y j).head 0)
        ((owned_intmulcarrystepadder_copyFrame x y j).cells 0 ((owned_intmulcarrystepadder_copyFrame x y j).head 0)) = (owned_intmulcarrystepadder_copyFrame x y j).cells 0
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
      have hwrite := owned_intmulcarrystepadder_tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
      rw [hl] at hwrite
      exact hwrite
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulcarrystepadder_copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = owned_intmulcarrystepadder_copyFrame x y j := by
  induction j with
  | zero => simpa using owned_intmulcarrystepadder_copy_start x y
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcarrystepadder_copy_step x y j (by omega)]


private theorem owned_intmulcarrystepadder_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcarrystepadder_copy_end_transition (a : Fin 3 → Sym) (hsep : a 0 = .sep)
    (hw : a 2 ≠ .start) : transition .copyX a =
      (.scanY, fun i => (a i, if i = 0 then .right else if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, hsep]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i <;> simp [owned_intmulcarrystepadder_safe_right, safe_stay, owned_intmulcarrystepadder_safe_left _ hw]

private theorem owned_intmulcarrystepadder_copy_end (x y : List Bool) :
    machine.step (owned_intmulcarrystepadder_copyFrame x y x.length) = owned_intmulcarrystepadder_scanFrame x y 0 := by
  have hsep : (owned_intmulcarrystepadder_copyFrame x y x.length).cells 0 ((owned_intmulcarrystepadder_copyFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : (owned_intmulcarrystepadder_copyFrame x y x.length).cells 2 ((owned_intmulcarrystepadder_copyFrame x y x.length).head 2) ≠ Sym.start := by
    change ((x.take x.length).map machine.bitSym).getD x.length machine.blank ≠ Sym.start
    rw [List.take_length, List.getD_eq_default _ _ (by simp)]
    decide
  have ht := owned_intmulcarrystepadder_copy_end_transition
    (fun i => (owned_intmulcarrystepadder_copyFrame x y x.length).cells i ((owned_intmulcarrystepadder_copyFrame x y x.length).head i)) hsep hw
  change transition (owned_intmulcarrystepadder_copyFrame x y x.length).state
    (fun i => (owned_intmulcarrystepadder_copyFrame x y x.length).cells i ((owned_intmulcarrystepadder_copyFrame x y x.length).head i)) = _ at ht
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcarrystepadder_copyFrame x y x.length).cells i) ((owned_intmulcarrystepadder_copyFrame x y x.length).head i)
      ((owned_intmulcarrystepadder_copyFrame x y x.length).cells i ((owned_intmulcarrystepadder_copyFrame x y x.length).head i)) = (owned_intmulcarrystepadder_scanFrame x y 0).cells i
    rw [Function.update_eq_self]
    fin_cases i <;> simp only [owned_intmulcarrystepadder_copyFrame, owned_intmulcarrystepadder_scanFrame, List.take_length]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcarrystepadder_copyFrame, owned_intmulcarrystepadder_scanFrame]

private theorem owned_intmulcarrystepadder_scan_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (owned_intmulcarrystepadder_scanFrame x y j) = owned_intmulcarrystepadder_scanFrame x y (j + 1) := by
  have hinput : (owned_intmulcarrystepadder_scanFrame x y j).cells 0 ((owned_intmulcarrystepadder_scanFrame x y j).head 0) = machine.bitSym y[j] := by
    change (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
      (x.length + 2 + j) = _
    rw [show x.length + 2 + j = (x.length + 1 + j) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show x.length + 1 + j - x.length = j + 1 by omega,
      List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (owned_intmulcarrystepadder_scanFrame x y j).cells 0 ((owned_intmulcarrystepadder_scanFrame x y j).head 0) = Sym.zero ∨
      (owned_intmulcarrystepadder_scanFrame x y j).cells 0 ((owned_intmulcarrystepadder_scanFrame x y j).head 0) = Sym.one := by
    rw [hinput]
    cases y[j] <;> simp [MultitapeTM.bitSym]
  have ht := owned_intmulcarrystepadder_scan_bit_transition
    (fun i => (owned_intmulcarrystepadder_scanFrame x y j).cells i ((owned_intmulcarrystepadder_scanFrame x y j).head i)) hb
  change transition (owned_intmulcarrystepadder_scanFrame x y j).state
    (fun i => (owned_intmulcarrystepadder_scanFrame x y j).cells i ((owned_intmulcarrystepadder_scanFrame x y j).head i)) = _ at ht
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcarrystepadder_scanFrame x y j).cells i) ((owned_intmulcarrystepadder_scanFrame x y j).head i)
      ((owned_intmulcarrystepadder_scanFrame x y j).cells i ((owned_intmulcarrystepadder_scanFrame x y j).head i)) = (owned_intmulcarrystepadder_scanFrame x y (j + 1)).cells i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcarrystepadder_scanFrame] <;> omega

private theorem owned_intmulcarrystepadder_scan_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (owned_intmulcarrystepadder_scanFrame x y 0) = owned_intmulcarrystepadder_scanFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcarrystepadder_scan_step x y j (by omega)]


/-- A reverse-addition frame with unprocessed little-endian operands `xs,ys`,
fixed processed operand suffixes, and a completed output suffix. -/
private def owned_intmulcarrystepadder_rippleFrame (X xs ys dx dy out : List Bool) (c : Bool) : machine.Cfg where
  state := .add c
  cells := fun i => if i = 0 then
      machine.tapeOf (X.map machine.bitSym ++ machine.sep :: (ys.reverse ++ dy).map machine.bitSym)
    else if i = 2 then machine.tapeOf ((xs.reverse ++ dx).map machine.bitSym)
    else machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++ out.map machine.bitSym)
  head := fun i => if i = 0 then X.length + 1 + ys.length
    else if i = 2 then xs.length else xs.length + 1

private theorem owned_intmulcarrystepadder_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcarrystepadder_decode_bit (b : Bool) : decode (machine.bitSym b) = b := by
  cases b <;> decide

private theorem owned_intmulcarrystepadder_encode_bit (b : Bool) : encode b = machine.bitSym b := rfl

private theorem owned_intmulcarrystepadder_bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem owned_intmulcarrystepadder_add_bit_transition (a : Fin 3 → Sym) (x y c : Bool)
    (hx : a 2 = machine.bitSym x) (hy : a 0 = machine.bitSym y) (ho : a 1 = .blank) :
    transition (.add c) a = (.add (IntMul.BinaryAdder.carryBit x y c), fun i =>
      (if i = 1 then machine.bitSym (IntMul.BinaryAdder.sumBit x y c) else a i, .left)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (owned_intmulcarrystepadder_bit_ne_start x)]
  simp only [owned_intmulcarrystepadder_decode_bit, hy]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .left = (a 0, .left)
    rw [hy]
    exact owned_intmulcarrystepadder_safe_left _ (owned_intmulcarrystepadder_bit_ne_start y)
  · change safeStep (a 1) (machine.bitSym (IntMul.BinaryAdder.sumBit x y c)) .left =
      (machine.bitSym (IntMul.BinaryAdder.sumBit x y c), .left)
    rw [ho]
    cases IntMul.BinaryAdder.sumBit x y c <;> decide
  · change safeStep (a 2) (a 2) .left = (a 2, .left)
    rw [hx]
    exact owned_intmulcarrystepadder_safe_left _ (owned_intmulcarrystepadder_bit_ne_start x)

private theorem owned_intmulcarrystepadder_ripple_step (X xs ys dx dy out : List Bool) (a b c : Bool) :
    machine.step (owned_intmulcarrystepadder_rippleFrame X (a :: xs) (b :: ys) dx dy out c) =
      owned_intmulcarrystepadder_rippleFrame X xs ys (a :: dx) (b :: dy)
        (IntMul.BinaryAdder.sumBit a b c :: out) (IntMul.BinaryAdder.carryBit a b c) := by
  let f := owned_intmulcarrystepadder_rippleFrame X (a :: xs) (b :: ys) dx dy out c
  have hx : f.cells 2 (f.head 2) = machine.bitSym a := by
    change (machine.tapeOf (((a :: xs).reverse ++ dx).map machine.bitSym)) (xs.length + 1) = _
    simp only [MultitapeTM.tapeOf]
    exact owned_intmulcarrystepadder_reverse_last a xs dx
  have hy : f.cells 0 (f.head 0) = machine.bitSym b := by
    change (machine.tapeOf (X.map machine.bitSym ++ machine.sep :: ((b :: ys).reverse ++ dy).map machine.bitSym))
      (X.length + 1 + (ys.length + 1)) = _
    rw [show X.length + 1 + (ys.length + 1) = (X.length + 1 + ys.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show X.length + 1 + ys.length - X.length = ys.length + 1 by omega,
      List.getD_cons_succ]
    exact owned_intmulcarrystepadder_reverse_last b ys dy
  have ho : f.cells 1 (f.head 1) = Sym.blank := by
    change (List.replicate ((a :: xs).length + 1) Sym.blank ++ out.map machine.bitSym).getD
      (a :: xs).length machine.blank = Sym.blank
    rw [List.getD_append _ _ _ _ (by simp only [List.length_replicate]; omega)]
    exact List.getD_replicate Sym.blank (by omega)
  have ht := owned_intmulcarrystepadder_add_bit_transition (fun i => f.cells i (f.head i)) a b c hx hy ho
  change transition (owned_intmulcarrystepadder_rippleFrame X (a :: xs) (b :: ys) dx dy out c).state
    (fun i => (owned_intmulcarrystepadder_rippleFrame X (a :: xs) (b :: ys) dx dy out c).cells i
      ((owned_intmulcarrystepadder_rippleFrame X (a :: xs) (b :: ys) dx dy out c).head i)) = _ at ht
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update (f.cells 0) (f.head 0) (f.cells 0 (f.head 0)) = _
      rw [Function.update_eq_self]
      simp [f, owned_intmulcarrystepadder_rippleFrame, List.reverse_cons, List.append_assoc]
    · change Function.update
        (machine.tapeOf (List.replicate (xs.length + 2) Sym.blank ++ out.map machine.bitSym))
        (xs.length + 2) (machine.bitSym (IntMul.BinaryAdder.sumBit a b c)) =
        machine.tapeOf (List.replicate (xs.length + 1) Sym.blank ++
          (IntMul.BinaryAdder.sumBit a b c :: out).map machine.bitSym)
      rw [show xs.length + 2 = (xs.length + 1) + 1 by omega,
        List.replicate_succ', List.append_assoc]
      simpa only [List.map_cons, List.length_replicate, List.singleton_append] using
        owned_intmulcarrystepadder_tape_replace_after_prefix machine (List.replicate (xs.length + 1) Sym.blank)
          (out.map machine.bitSym) Sym.blank (machine.bitSym (IntMul.BinaryAdder.sumBit a b c))
    · change Function.update (f.cells 2) (f.head 2) (f.cells 2 (f.head 2)) = _
      rw [Function.update_eq_self]
      simp [f, owned_intmulcarrystepadder_rippleFrame, List.reverse_cons, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [f, owned_intmulcarrystepadder_rippleFrame] <;> omega


private theorem owned_intmulcarrystepadder_add_end_transition (a : Fin 3 → Sym) (c : Bool)
    (hw : a 2 = .start) (ho : a 1 = .blank) :
    transition (.add c) a = (.halt, fun i =>
      (if i = 1 then machine.bitSym c else a i, .stay)) := by
  simp only [transition, rawTransition, hw, if_true]
  congr 1
  funext i
  by_cases hi : i = 1
  · subst i
    simp only [if_pos rfl, owned_intmulcarrystepadder_encode_bit]
    rw [ho]
    cases c <;> decide
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcarrystepadder_ripple_stop (X dx dy out : List Bool) (c : Bool) :
    (machine.step (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c)).state = .halt ∧
      (machine.step (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c)).cells machine.outTape =
        machine.tapeOf ((c :: out).map machine.bitSym) := by
  have hw : (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 2
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 2) = Sym.start := rfl
  have ho : (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 1
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 1) = Sym.blank := rfl
  have ht := owned_intmulcarrystepadder_add_end_transition
    (fun i => (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells i
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head i)) c hw ho
  change transition (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).state
    (fun i => (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells i
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head i)) = _ at ht
  constructor
  · simp only [MultitapeTM.step, ht]
  · simp only [MultitapeTM.step, ht]
    change Function.update (machine.tapeOf (Sym.blank :: out.map machine.bitSym)) 1
      (machine.bitSym c) = machine.tapeOf ((c :: out).map machine.bitSym)
    simpa only [List.length_nil, List.nil_append, Nat.zero_add, List.map_cons] using
      owned_intmulcarrystepadder_tape_replace_after_prefix machine [] (out.map machine.bitSym) Sym.blank (machine.bitSym c)

private theorem owned_intmulcarrystepadder_ripple_run (X xs ys dx dy out : List Bool) (c : Bool)
    (h : xs.length = ys.length) :
    (machine.step^[xs.length + 1] (owned_intmulcarrystepadder_rippleFrame X xs ys dx dy out c)).state = .halt ∧
      (machine.step^[xs.length + 1] (owned_intmulcarrystepadder_rippleFrame X xs ys dx dy out c)).cells machine.outTape =
        machine.tapeOf (((IntMul.BinaryAdder.addLittle xs ys c).reverse ++ out).map machine.bitSym) := by
  induction xs generalizing ys dx dy out c with
  | nil =>
      cases ys with
      | nil => simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
          IntMul.BinaryAdder.addLittle, List.reverse_singleton, List.singleton_append] using
          owned_intmulcarrystepadder_ripple_stop X dx dy out c
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [show (a :: xs).length + 1 = (xs.length + 1) + 1 by simp,
            Function.iterate_succ_apply, owned_intmulcarrystepadder_ripple_step]
          simpa only [IntMul.BinaryAdder.addLittle, List.reverse_cons,
            List.append_assoc, List.singleton_append] using
            ih ys (a :: dx) (b :: dy) (IntMul.BinaryAdder.sumBit a b c :: out)
              (IntMul.BinaryAdder.carryBit a b c) ht

private theorem owned_intmulcarrystepadder_scan_end_transition (a : Fin 3 → Sym) (hb : a 0 = .blank) :
    transition .scanY a = (.add false, fun i => (a i, if i = 0 then .left else .stay)) := by
  simp only [transition, rawTransition, hb]
  rw [if_neg (by decide : ¬(Sym.blank = Sym.zero ∨ Sym.blank = Sym.one))]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    rw [hb]
    exact owned_intmulcarrystepadder_safe_left Sym.blank (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcarrystepadder_blank_tape (n : ℕ) :
    machine.tapeOf (List.replicate n Sym.blank) = machine.tapeOf [] := by
  funext p
  cases p <;> simp [MultitapeTM.tapeOf, List.getD_eq_getElem?_getD]

private theorem owned_intmulcarrystepadder_scan_end (x y : List Bool) (h : x.length = y.length) :
    machine.step (owned_intmulcarrystepadder_scanFrame x y y.length) = owned_intmulcarrystepadder_rippleFrame x x.reverse y.reverse [] [] [] false := by
  have hb : (owned_intmulcarrystepadder_scanFrame x y y.length).cells 0 ((owned_intmulcarrystepadder_scanFrame x y y.length).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
      (x.length + 2 + y.length) = Sym.blank
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    exact List.getD_eq_default _ _ (by simp; omega)
  have ht := owned_intmulcarrystepadder_scan_end_transition
    (fun i => (owned_intmulcarrystepadder_scanFrame x y y.length).cells i ((owned_intmulcarrystepadder_scanFrame x y y.length).head i)) hb
  change transition (owned_intmulcarrystepadder_scanFrame x y y.length).state
    (fun i => (owned_intmulcarrystepadder_scanFrame x y y.length).cells i ((owned_intmulcarrystepadder_scanFrame x y y.length).head i)) = _ at ht
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcarrystepadder_scanFrame x y y.length).cells i) ((owned_intmulcarrystepadder_scanFrame x y y.length).head i)
      ((owned_intmulcarrystepadder_scanFrame x y y.length).cells i ((owned_intmulcarrystepadder_scanFrame x y y.length).head i)) =
        (owned_intmulcarrystepadder_rippleFrame x x.reverse y.reverse [] [] [] false).cells i
    rw [Function.update_eq_self]
    fin_cases i
    · simp [owned_intmulcarrystepadder_scanFrame, owned_intmulcarrystepadder_rippleFrame]
    · simp [owned_intmulcarrystepadder_scanFrame, owned_intmulcarrystepadder_rippleFrame]
      exact (owned_intmulcarrystepadder_blank_tape _).symm
    · simp [owned_intmulcarrystepadder_scanFrame, owned_intmulcarrystepadder_rippleFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcarrystepadder_scanFrame, owned_intmulcarrystepadder_rippleFrame, h] <;> omega


end IntMul.TapeAdder

namespace IntMul.TapeAdder

open TapeCopy (Sym)

private def carrySumFrame (X oldx oldy out : List Bool) : machine.Cfg where
  state := .halt
  cells := fun i => if i=0 then machine.tapeOf (X.map machine.bitSym++Sym.sep::oldy.map machine.bitSym)
    else if i=2 then machine.tapeOf (oldx.map machine.bitSym)
    else machine.tapeOf (out.map machine.bitSym)
  head := fun i => if i=0 then X.length+1 else if i=2 then 0 else 1

private theorem owned_intmulcarrystepadder_carry_ripple_stop (X dx dy out : List Bool) (c : Bool) :
    machine.step (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c)=carrySumFrame X dx dy (c::out) := by
  have hw : (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 2
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 2)=Sym.start := rfl
  have ho : (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 1
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 1)=Sym.blank := rfl
  have ht := owned_intmulcarrystepadder_add_end_transition (fun i => (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells i
    ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head i)) c hw ho
  change transition (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).state
    (fun i => (owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells i
      ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head i))=_ at ht
  apply owned_intmulcarrystepadder_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 0)
        ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 0)
        ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 0 ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 0))=_
      rw [Function.update_eq_self]; simp [owned_intmulcarrystepadder_rippleFrame,carrySumFrame]
    · change Function.update (machine.tapeOf (Sym.blank::out.map machine.bitSym)) 1
        (machine.bitSym c)=machine.tapeOf ((c::out).map machine.bitSym)
      simpa only [List.length_nil,List.nil_append,Nat.zero_add,List.map_cons] using
        owned_intmulcarrystepadder_tape_replace_after_prefix machine [] (out.map machine.bitSym) Sym.blank (machine.bitSym c)
    · change Function.update ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 2)
        ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 2)
        ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).cells 2 ((owned_intmulcarrystepadder_rippleFrame X [] [] dx dy out c).head 2))=_
      rw [Function.update_eq_self]; simp [owned_intmulcarrystepadder_rippleFrame,carrySumFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [owned_intmulcarrystepadder_rippleFrame,carrySumFrame]

private theorem owned_intmulcarrystepadder_carry_ripple_run (X xs ys dx dy out : List Bool) (c : Bool)
    (h : xs.length=ys.length) :
    machine.step^[xs.length+1] (owned_intmulcarrystepadder_rippleFrame X xs ys dx dy out c)=
      carrySumFrame X (xs.reverse++dx) (ys.reverse++dy)
        ((BinaryAdder.addLittle xs ys c).reverse++out) := by
  induction xs generalizing ys dx dy out c with
  | nil =>
    cases ys with
    | nil => simpa only [List.length_nil,Nat.zero_add,Function.iterate_one,
        BinaryAdder.addLittle,List.reverse_singleton,List.singleton_append,List.nil_append,
        List.reverse_nil] using owned_intmulcarrystepadder_carry_ripple_stop X dx dy out c
    | cons b ys => simp at h
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      rw [show (a::xs).length+1=(xs.length+1)+1 by simp,
        Function.iterate_succ_apply,owned_intmulcarrystepadder_ripple_step]
      have hh : xs.length=ys.length := by simpa using h
      have hr := ih ys (a::dx) (b::dy) (BinaryAdder.sumBit a b c::out)
        (BinaryAdder.carryBit a b c) hh
      simpa only [BinaryAdder.addLittle,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

/-- The native adder's complete terminal configuration, owned as a helper
inside the carry-step proof so the following relay can use its actual heads. -/
private theorem carry_add_full (x y : List Bool) (h : x.length=y.length) :
    machine.step^[3*x.length+4] (machine.initCfg x y)=
      carrySumFrame x x y (bin (x.length+1) (val x+val y)) := by
  have hcopy : machine.step^[x.length+2] (machine.initCfg x y)=owned_intmulcarrystepadder_scanFrame x y 0 := by
    rw [show x.length+2=(x.length+1)+1 by omega,Function.iterate_succ_apply',
      owned_intmulcarrystepadder_copy_run x y x.length le_rfl,owned_intmulcarrystepadder_copy_end]
  have hscan : machine.step^[x.length+y.length+3] (machine.initCfg x y)=
      owned_intmulcarrystepadder_rippleFrame x x.reverse y.reverse [] [] [] false := by
    rw [show x.length+y.length+3=(y.length+(x.length+2))+1 by omega,
      Function.iterate_succ_apply',Function.iterate_add_apply,hcopy,
      owned_intmulcarrystepadder_scan_run x y y.length le_rfl,owned_intmulcarrystepadder_scan_end x y h]
  have hr := owned_intmulcarrystepadder_carry_ripple_run x x.reverse y.reverse [] [] [] false (by simpa using h)
  have hclock : 3*x.length+4=(x.reverse.length+1)+(x.length+y.length+3) := by
    simp only [List.length_reverse];omega
  rw [hclock,Function.iterate_add_apply,hscan]
  simpa only [List.append_nil,List.reverse_reverse,BinaryAdder.owned_intmulcarrystepadder_ripple_sum_bin x y h] using hr

end IntMul.TapeAdder


namespace IntMul.CarryStep

private theorem sum_length (x y : List Bool) : (sumWord x y).length=x.length+1 := by
  simp [sumWord,bin]

private theorem sum_value (x y : List Bool) (h : x.length=y.length) :
    val (sumWord x y)=val x+val y := by
  have hr := BinaryAdder.owned_intmulcarrystepadder_ripple_sum_spec x y h
  rw [BinaryAdder.owned_intmulcarrystepadder_ripple_sum_bin x y h] at hr
  exact hr.2

private theorem carry_value_split (x y z : List Bool) (h : x.length=y.length)
    (hB : blockSize z ≤ x.length+1) :
    val (digitWord x y z).reverse=(val x+val y)%(2^blockSize z) ∧
      val (carryWord x y z).reverse=(val x+val y)/(2^blockSize z) := by
  let s := sumWord x y
  let B := blockSize z
  let low := (s.reverse.take B).reverse
  let high := (s.reverse.drop B).reverse
  have hBs : B ≤ s.length := by simpa only [s,sum_length] using hB
  have hl : low.length=B := by
    simp only [low,List.length_reverse,List.length_take,Nat.min_eq_left hBs]
  have hlo : val low < 2^B := by
    rw [show low=(s.reverse.take B).reverse from rfl,BinaryAdder.owned_intmulcarrystepadder_val_reverse_little]
    have hb := BinaryAdder.owned_intmulcarrystepadder_little_value_bound (s.reverse.take B)
    simpa only [List.length_take,List.length_reverse,Nat.min_eq_left hBs] using hb
  have hd : high++low=s := by
    dsimp only [high,low]
    rw [←List.reverse_append,List.take_append_drop,List.reverse_reverse]
  have hv : val s=2^B*val high+val low := by
    calc
      val s=val (high++low) := congrArg val hd.symm
      _=2^B*val high+val low := by rw [BinaryAdder.owned_intmulcarrystepadder_val_append,hl]
  have hb : 0 < 2^B := by positivity
  have hs : val s=val x+val y := sum_value x y h
  change val low=(val x+val y)%(2^B) ∧ val high=(val x+val y)/(2^B)
  rw [←hs,hv]
  constructor
  · simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hlo]
  · rw [Nat.mul_add_div hb,Nat.div_eq_of_lt hlo,Nat.add_zero]

end IntMul.CarryStep



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




namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

/-- Full live stream configuration, including emitted prefix and saved template. -/
private def streamFrame (x y bits : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((x.take j).map machine.bitSym)
    else if i = 2 then machine.tapeOf (Sym.sep :: (bits.reverse.map machine.bitSym ++ [Sym.sep]))
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
  head := fun i => if i = 0 ∨ i = 1 then j + 1 else y.length + 1

private def owned_intmulcountedstreamsetup_scanXFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .scanX
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym) else machine.tapeOf []
  head := fun i => if i = 0 then j + 1 else 1

private def owned_intmulcountedstreamsetup_copyYFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyY
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2 + j else if i = 2 ∨ i = 3 then j + 2 else 1

private def owned_intmulcountedstreamsetup_rewindInputFrame (x y : List Bool) (p : ℕ) : machine.Cfg where
  state := .rewindInput
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
    else machine.tapeOf []
  head := fun i => if i = 0 then p else if i = 2 ∨ i = 3 then y.length + 1 else 1

private theorem owned_intmulcountedstreamsetup_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamsetup_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamsetup_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamsetup_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private theorem owned_intmulcountedstreamsetup_initial_transition (a : Fin 4 → Sym) :
    transition .start a = (.scanX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, owned_intmulcountedstreamsetup_safe_right]

private theorem owned_intmulcountedstreamsetup_setup_start (x y : List Bool) :
    machine.step (machine.initCfg x y) = owned_intmulcountedstreamsetup_scanXFrame x y 0 := by
  have ht := owned_intmulcountedstreamsetup_initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
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
    funext i
    fin_cases i <;> rfl

private theorem owned_intmulcountedstreamsetup_scan_bit_transition (a : Fin 4 → Sym)
    (h : a 0 = .zero ∨ a 0 = .one) :
    transition .scanX a = (.scanX, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, owned_intmulcountedstreamsetup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_scan_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (owned_intmulcountedstreamsetup_scanXFrame x y j) = owned_intmulcountedstreamsetup_scanXFrame x y (j + 1) := by
  have hr : (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = Sym.zero ∨
      (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = Sym.one := by
    rw [hr]
    cases x[j] <;> decide
  have ht := owned_intmulcountedstreamsetup_scan_bit_transition
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) hb
  change transition (owned_intmulcountedstreamsetup_scanXFrame x y j).state
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_scanXFrame x y j).cells i) ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)
      ((owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [owned_intmulcountedstreamsetup_scanXFrame, hi]

private theorem owned_intmulcountedstreamsetup_scan_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = owned_intmulcountedstreamsetup_scanXFrame x y j := by
  induction j with
  | zero => simpa using owned_intmulcountedstreamsetup_setup_start x y
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamsetup_scan_step x y j (by omega)]


private theorem owned_intmulcountedstreamsetup_scan_end_transition (a : Fin 4 → Sym) (hs : a 0 = .sep)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .scanX a = (.copyY, fun i =>
      (if i = 2 ∨ i = 3 then .sep else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, hs]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamsetup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .right = (Sym.sep, .right)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .right = (Sym.sep, .right)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem owned_intmulcountedstreamsetup_scan_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_scanXFrame x y x.length) = owned_intmulcountedstreamsetup_copyYFrame x y 0 := by
  have hs : (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp [owned_intmulcountedstreamsetup_scanXFrame, h0, MultitapeTM.tapeOf]
  have ht := owned_intmulcountedstreamsetup_scan_end_transition
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i)) hs hw
  change transition (owned_intmulcountedstreamsetup_scanXFrame x y x.length).state
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0) ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0)
        ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf []) 1 Sym.sep = machine.tapeOf [Sym.sep]
      exact owned_intmulcountedstreamsetup_tapeOf_append_one machine [] Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_scanXFrame, owned_intmulcountedstreamsetup_copyYFrame]

private theorem owned_intmulcountedstreamsetup_copy_bit_transition (a : Fin 4 → Sym) (b : Bool) (hb : a 0 = machine.bitSym b)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .copyY a = (.copyY, fun i =>
      (if i = 2 ∨ i = 3 then machine.bitSym b else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamsetup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 2 (Or.inl rfl), hb]
    cases b <;> decide
  · change safeStep (a 3) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 3 (Or.inr rfl), hb]
    cases b <;> decide

private theorem owned_intmulcountedstreamsetup_copy_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (owned_intmulcountedstreamsetup_copyYFrame x y j) = owned_intmulcountedstreamsetup_copyYFrame x y (j + 1) := by
  have hl : (Sym.sep :: (y.take j).map machine.bitSym).length = j + 1 := by
    simp [Nat.min_eq_left hj.le]
  have hr : (owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0) = machine.bitSym y[j] := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)) (x.length + 2 + j) = _
    rw [show x.length + 2 + j = (x.length + 1 + j) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show x.length + 1 + j - x.length = j + 1 by omega, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [owned_intmulcountedstreamsetup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take j).map machine.bitSym).getD (j + 1) machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcountedstreamsetup_copy_bit_transition
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i)) y[j] hr hw
  change transition (owned_intmulcountedstreamsetup_copyYFrame x y j).state
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i)) = _ at ht
  have hnew : Sym.sep :: (y.take (j + 1)).map machine.bitSym =
      (Sym.sep :: (y.take j).map machine.bitSym) ++ [machine.bitSym y[j]] := by
    rw [List.take_succ_eq_append_getElem hj, List.map_append]
    rfl
  have hwrite := owned_intmulcountedstreamsetup_tapeOf_append_one machine (Sym.sep :: (y.take j).map machine.bitSym) (machine.bitSym y[j])
  rw [hl] at hwrite
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0) ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0)
        ((owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf (Sym.sep :: (y.take j).map machine.bitSym)) (j + 2)
        (machine.bitSym y[j]) = machine.tapeOf (Sym.sep :: (y.take (j + 1)).map machine.bitSym)
      rw [hnew]
      exact hwrite
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_copyYFrame] <;> omega

private theorem owned_intmulcountedstreamsetup_copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (owned_intmulcountedstreamsetup_copyYFrame x y 0) = owned_intmulcountedstreamsetup_copyYFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamsetup_copy_step x y j (by omega)]


private theorem owned_intmulcountedstreamsetup_copy_end_transition (a : Fin 4 → Sym) (hs : a 0 = .blank)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .copyY a = (.rewindInput, fun i =>
      (if i = 2 ∨ i = 3 then .sep else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hs]
  rw [if_neg (by decide : ¬(Sym.blank = Sym.zero ∨ Sym.blank = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .left = (a 0, .left)
    rw [hs]
    exact owned_intmulcountedstreamsetup_safe_left _ (by decide)
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .left = (Sym.sep, .left)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .left = (Sym.sep, .left)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem owned_intmulcountedstreamsetup_copy_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_copyYFrame x y y.length) = owned_intmulcountedstreamsetup_rewindInputFrame x y (x.length + y.length + 1) := by
  have hs : (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym))
      (x.length + 2 + y.length) = _
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    exact List.getD_eq_default _ _ (by simp; omega)
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [owned_intmulcountedstreamsetup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take y.length).map machine.bitSym).getD (y.length + 1) machine.blank = _
    rw [List.take_length]
    exact List.getD_eq_default _ _ (by simp)
  have ht := owned_intmulcountedstreamsetup_copy_end_transition
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i)) hs hw
  change transition (owned_intmulcountedstreamsetup_copyYFrame x y y.length).state
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0) ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0)
        ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf (Sym.sep :: (y.take y.length).map machine.bitSym))
        (y.length + 2) Sym.sep = machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
      simpa [List.take_length] using owned_intmulcountedstreamsetup_tapeOf_append_one machine (Sym.sep :: y.map machine.bitSym) Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_copyYFrame, owned_intmulcountedstreamsetup_rewindInputFrame] <;> omega

private theorem owned_intmulcountedstreamsetup_input_getD_ne_start (x y : List Bool) (p : ℕ) :
    (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD p machine.blank ≠ Sym.start := by
  let w := x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym
  have hw : ∀ a ∈ w, a ≠ Sym.start := by
    intro a ha
    rcases List.mem_append.mp ha with hx | hy
    · rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
      cases b <;> decide
    · rcases List.mem_cons.mp hy with hs | hy
      · subst a; decide
      · rcases List.mem_map.mp hy with ⟨b, _, rfl⟩
        cases b <;> decide
  change w.getD p machine.blank ≠ Sym.start
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact hw _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem owned_intmulcountedstreamsetup_rewind_transition (a : Fin 4 → Sym) (h : a 0 ≠ .start) :
    transition .rewindInput a = (.rewindInput, fun i => (a i, if i = 0 then .left else .stay)) := by
  simp only [transition, rawTransition, if_neg h]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    exact owned_intmulcountedstreamsetup_safe_left _ h
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_rewind_step (x y : List Bool) (p : ℕ) :
    machine.step (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)) = owned_intmulcountedstreamsetup_rewindInputFrame x y p := by
  have hn : (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells 0 ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head 0) ≠ Sym.start :=
    owned_intmulcountedstreamsetup_input_getD_ne_start x y p
  have ht := owned_intmulcountedstreamsetup_rewind_transition
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) hn
  change transition (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).state
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i) ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)
      ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, hi]

private theorem owned_intmulcountedstreamsetup_rewind_run (x y : List Bool) (p : ℕ) :
    machine.step^[p] (owned_intmulcountedstreamsetup_rewindInputFrame x y p) = owned_intmulcountedstreamsetup_rewindInputFrame x y 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply, owned_intmulcountedstreamsetup_rewind_step, ih]

private theorem owned_intmulcountedstreamsetup_rewind_end_transition (a : Fin 4 → Sym) (h : a 0 = .start) :
    transition .rewindInput a = (.emit, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, owned_intmulcountedstreamsetup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_rewind_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_rewindInputFrame x y 0) = streamFrame x y y.reverse 0 .emit := by
  have hs : (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells 0 ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head 0) = Sym.start := rfl
  have ht := owned_intmulcountedstreamsetup_rewind_end_transition
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) hs
  change transition (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).state
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i) ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)
      ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, streamFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, streamFrame]

/-- Exact setup cost includes both operand/descriptor scans, the saved copy,
separator writes, and the input-head return to the first payload bit. -/
private theorem setup_correct (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      streamFrame x y y.reverse 0 .emit := by
  have hscan : machine.step^[x.length + 2] (machine.initCfg x y) = owned_intmulcountedstreamsetup_copyYFrame x y 0 := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply', owned_intmulcountedstreamsetup_scan_run x y x.length le_rfl, owned_intmulcountedstreamsetup_scan_end]
  have hcopy : machine.step^[x.length + y.length + 3] (machine.initCfg x y) =
      owned_intmulcountedstreamsetup_rewindInputFrame x y (x.length + y.length + 1) := by
    rw [show x.length + y.length + 3 = (y.length + (x.length + 2)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hscan,
      owned_intmulcountedstreamsetup_copy_run x y y.length le_rfl, owned_intmulcountedstreamsetup_copy_end]
  rw [show 2 * x.length + 2 * y.length + 5 =
      ((x.length + y.length + 1) + (x.length + y.length + 3)) + 1 by omega,
    Function.iterate_succ_apply', Function.iterate_add_apply, hcopy, owned_intmulcountedstreamsetup_rewind_run, owned_intmulcountedstreamsetup_rewind_end]

end IntMul.CountedStream



/-! Decrement arithmetic adapted from the frozen public CounterArithmetic
module, with Boolean direction fixed to decrement and the campaign word value.
The integrated controller and actual campaign-machine trace are separate. -/
namespace IntMul.CountedStream

open IntMul.BinaryAdder (littleVal)

private theorem updated_nil : updated [] = [] := rfl

private theorem updated_zero (bs : List Bool) : updated (false :: bs) = true :: updated bs := by
  simp [updated, carryLength, stopTail, List.replicate_succ]

private theorem updated_one (bs : List Bool) : updated (true :: bs) = false :: bs := by
  simp [updated, carryLength, stopTail]

private theorem updated_length (bits : List Bool) : (updated bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]; simp [ih]
      · rw [updated_one]; rfl

private theorem carry_length_le (bits : List Bool) : carryLength bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [carryLength, List.length_cons]; split_ifs <;> omega

private theorem potential_le (bits : List Bool) : potential bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [potential, List.length_cons]; split_ifs <;> omega

private theorem potential_accounting (bits : List Bool) :
    carryLength bits + potential (updated bits) ≤ potential bits + 1 := by
  induction bits with
  | nil => simp [carryLength, potential, updated_nil]
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [carryLength, potential, if_true, Bool.true_eq_false, if_false]
        omega
      · rw [updated_one]
        simp [carryLength, potential, Nat.add_comm]

private theorem amortized_step (bits : List Bool) :
    counterSteps bits + 2 * potential (updated bits) ≤ 4 + 2 * potential bits := by
  have h := potential_accounting bits
  unfold counterSteps
  omega

private theorem iterate_counter_length (n : ℕ) (bits : List Bool) :
    (iterateCounter n bits).length = bits.length := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => rw [iterateCounter, ih, updated_length]

private theorem amortized_total (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits + 2 * potential (iterateCounter n bits) ≤ 4 * n + 2 * potential bits := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have h := amortized_step bits
      have hn := ih (updated bits)
      simp only [totalCounterSteps, iterateCounter]
      omega

private theorem total_counter_steps_bound (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits ≤ 4 * n + 2 * bits.length := by
  have h := amortized_total n bits
  have hp := potential_le bits
  omega

/-- Exact decrement, including the fixed-width wrap term on underflow. -/
private theorem decrement_value (bits : List Bool) :
    value bits + (if underflow bits then 2 ^ bits.length else 0) = value (updated bits) + 1 := by
  induction bits with
  | nil => simp [updated_nil, value, littleVal, underflow]
  | cons b bs ih =>
      simp only [value] at ih
      cases b
      · rw [updated_zero]
        simp only [value, littleVal, underflow, Bool.toNat_false, Bool.toNat_true,
          if_true, List.length_cons, pow_succ]
        cases ho : underflow bs <;> simp [ho] at ih ⊢ <;> omega
      · simp [updated_one, value, littleVal, underflow, Nat.add_comm]

private theorem underflow_iff_zero (bits : List Bool) : underflow bits = true ↔ value bits = 0 := by
  induction bits with
  | nil => simp [underflow, value, littleVal]
  | cons b bs ih => cases b <;> simp [underflow, value, littleVal, ih]

private theorem underflow_all_ones (bits : List Bool) (h : underflow bits = true) :
    updated bits = List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [underflow, if_true] at h
        rw [ih h, List.length_cons, List.replicate_succ]
      · simp [underflow] at h

private theorem decrement_positive (bits : List Bool) (h : 0 < value bits) :
    underflow bits = false ∧ value (updated bits) + 1 = value bits := by
  have hn : underflow bits ≠ true := by
    intro hflag
    have := (underflow_iff_zero bits).mp hflag
    omega
  have hf : underflow bits = false := by cases hflag : underflow bits <;> simp_all
  refine ⟨hf, ?_⟩
  have hv := decrement_value bits
  simpa [hf] using hv.symm

private theorem countdown_value (bits : List Bool) (n : ℕ) (hn : n ≤ value bits) :
    value (iterateCounter n bits) = value bits - n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hv := (decrement_positive bits hp).2
      have hnext : n ≤ value (updated bits) := by omega
      rw [iterateCounter, ih (updated bits) hnext]
      omega

private theorem countdown_not_finished (bits : List Bool) (n : ℕ) (hn : n < value bits) :
    underflow (iterateCounter n bits) = false := by
  have hv := countdown_value bits n hn.le
  exact (decrement_positive _ (by omega)).1

private theorem countdown_final_underflow (bits : List Bool) :
    underflow (iterateCounter (value bits) bits) = true := by
  apply (underflow_iff_zero _).mpr
  rw [countdown_value bits (value bits) le_rfl]
  omega


private theorem total_counter_steps_succ (n : ℕ) (bits : List Bool) :
    totalCounterSteps (n + 1) bits = totalCounterSteps n bits + counterSteps (iterateCounter n bits) := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      change counterSteps bits + totalCounterSteps (n + 1) (updated bits) =
        (counterSteps bits + totalCounterSteps n (updated bits)) + counterSteps (iterateCounter n (updated bits))
      rw [ih (updated bits)]
      omega

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem owned_intmulcountedstreamcounter_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem owned_intmulcountedstreamcounter_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamcounter_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem owned_intmulcountedstreamcounter_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamcounter_carry_zero_transition (a : Fin 4 → Sym) (h : a 2 = .zero) :
    transition .carry a = (.carry, fun i =>
      (if i = 2 then .one else a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_carry_one_transition (a : Fin 4 → Sym) (h : a 2 = .one) :
    transition .carry a = (.rewind false, fun i =>
      (if i = 2 then .zero else a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.one = Sym.zero)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_carry_sep_transition (a : Fin 4 → Sym) (h : a 2 = .sep) :
    transition .carry a = (.rewind true, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.sep = Sym.zero),
    if_neg (by decide : ¬Sym.sep = Sym.one)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, owned_intmulcountedstreamcounter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_rewind_bit_transition (a : Fin 4 → Sym) (f : Bool)
    (h : a 2 = .zero ∨ a 2 = .one) :
    transition (.rewind f) a = (.rewind f, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, owned_intmulcountedstreamcounter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_rewind_sep_transition (a : Fin 4 → Sym) (f : Bool) (h : a 2 = .sep) :
    transition (.rewind f) a = (.done f, fun i => (a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    exact owned_intmulcountedstreamcounter_safe_left _ (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_bit_mem (b : Bool) : machine.bitSym b = Sym.zero ∨ machine.bitSym b = Sym.one := by
  cases b <;> decide

/-- Reading the least significant remaining bit after the left delimiter. -/
private theorem owned_intmulcountedstreamcounter_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamcounter_carry_read (base : machine.Cfg) (b : Bool) (bs done : List Bool) :
    (carryFrame base (b :: bs) done).cells 2 ((carryFrame base (b :: bs) done).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
    (bs.length + 2) = machine.bitSym b
  rw [show bs.length + 2 = (bs.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  exact owned_intmulcountedstreamcounter_reverse_last b bs done

private theorem owned_intmulcountedstreamcounter_carry_zero_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (false :: bs) done) = carryFrame base bs (true :: done) := by
  have hz : (carryFrame base (false :: bs) done).cells 2
      ((carryFrame base (false :: bs) done).head 2) = Sym.zero := owned_intmulcountedstreamcounter_carry_read base false bs done
  have ht := owned_intmulcountedstreamcounter_carry_zero_transition
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) hz
  change transition (carryFrame base (false :: bs) done).state
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.one =
          machine.tapeOf (Sym.sep :: ((bs.reverse ++ true :: done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        owned_intmulcountedstreamcounter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.zero Sym.one
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (false :: bs) done).cells i)
        ((carryFrame base (false :: bs) done).head i)
        ((carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame]
    · simp [carryFrame, hi]


private theorem owned_intmulcountedstreamcounter_carry_one_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (true :: bs) done) = rewindFrame base false (false :: bs).reverse done := by
  have ho : (carryFrame base (true :: bs) done).cells 2
      ((carryFrame base (true :: bs) done).head 2) = Sym.one := owned_intmulcountedstreamcounter_carry_read base true bs done
  have ht := owned_intmulcountedstreamcounter_carry_one_transition
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) ho
  change transition (carryFrame base (true :: bs) done).state
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((true :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.zero =
          machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        owned_intmulcountedstreamcounter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.one Sym.zero
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (true :: bs) done).cells i)
        ((carryFrame base (true :: bs) done).head i)
        ((carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, rewindFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame, rewindFrame]
    · simp [carryFrame, rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_carry_nil_step (base : machine.Cfg) (done : List Bool) :
    machine.step (carryFrame base [] done) = rewindFrame base true [] done := by
  have hm : (carryFrame base [] done).cells 2 ((carryFrame base [] done).head 2) = Sym.sep := rfl
  have ht := owned_intmulcountedstreamcounter_carry_sep_transition
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) hm
  change transition (carryFrame base [] done).state
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((carryFrame base [] done).cells i) ((carryFrame base [] done).head i)
      ((carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _
    rw [Function.update_eq_self]
    simp [carryFrame, rewindFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [carryFrame, rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_read (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep])))
    (pre.length + 2) = machine.bitSym b
  rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamcounter_rewind_step (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    machine.step (rewindFrame base f pre (b :: bs)) = rewindFrame base f (pre ++ [b]) bs := by
  have hb : (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.zero ∨
      (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.one := by
    rw [owned_intmulcountedstreamcounter_rewind_read]
    exact owned_intmulcountedstreamcounter_bit_mem b
  have ht := owned_intmulcountedstreamcounter_rewind_bit_transition
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) f hb
  change transition (rewindFrame base f pre (b :: bs)).state
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre (b :: bs)).cells i) ((rewindFrame base f pre (b :: bs)).head i)
      ((rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_end (base : machine.Cfg) (f : Bool) (pre : List Bool) :
    machine.step (rewindFrame base f pre []) = counterFrame base (.done f) pre.reverse := by
  have hs : (rewindFrame base f pre []).cells 2 ((rewindFrame base f pre []).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: ((pre ++ []).map machine.bitSym ++ [Sym.sep])))
      (pre.length + 2) = Sym.sep
    rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ, List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamcounter_rewind_sep_transition
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) f hs
  change transition (rewindFrame base f pre []).state
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre []).cells i) ((rewindFrame base f pre []).head i)
      ((rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, counterFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, counterFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_run (base : machine.Cfg) (f : Bool) (pre right : List Bool) :
    machine.step^[right.length + 1] (rewindFrame base f pre right) =
      counterFrame base (.done f) (pre ++ right).reverse := by
  induction right generalizing pre with
  | nil => simpa using owned_intmulcountedstreamcounter_rewind_end base f pre
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp,
        Function.iterate_succ_apply, owned_intmulcountedstreamcounter_rewind_step, ih]
      simp [List.append_assoc]

private theorem owned_intmulcountedstreamcounter_carry_run (base : machine.Cfg) (bits done : List Bool) :
    machine.step^[carryLength bits + 1] (carryFrame base bits done) =
      rewindFrame base (underflow bits) (stopTail bits).reverse
        (List.replicate (carryLength bits) true ++ done) := by
  induction bits generalizing done with
  | nil => simpa [carryLength, underflow, stopTail] using owned_intmulcountedstreamcounter_carry_nil_step base done
  | cons b bs ih =>
      cases b
      · simp only [carryLength, underflow, stopTail, if_true]
        rw [Function.iterate_succ_apply, owned_intmulcountedstreamcounter_carry_zero_step, ih]
        simp [List.replicate_succ', List.append_assoc]
      · simpa [carryLength, underflow, stopTail] using owned_intmulcountedstreamcounter_carry_one_step base bs done

/-- The actual decrement table restores the head and preserves all other tapes.
Its exact count includes propagation, resolution, and the full head return. -/
private theorem counter_correct (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits) =
      counterFrame base (.done (underflow bits)) (updated bits) := by
  have hc : counterFrame base .carry bits = carryFrame base bits [] := by
    apply owned_intmulcountedstreamcounter_cfg_ext <;> simp [counterFrame, carryFrame]
  have ht : counterSteps bits = (carryLength bits + 1) + (carryLength bits + 1) := by
    unfold counterSteps
    omega
  rw [hc, ht, Function.iterate_add_apply, owned_intmulcountedstreamcounter_carry_run]
  simp only [List.append_nil]
  have hr := owned_intmulcountedstreamcounter_rewind_run base (underflow bits) (stopTail bits).reverse (List.replicate (carryLength bits) true)
  simpa [updated, List.reverse_append, List.reverse_replicate] using hr

end IntMul.CountedStream




namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem owned_intmulcountedstreamreset_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamreset_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamreset_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamreset_bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem owned_intmulcountedstreamreset_reset_left_transition (a : Fin 4 → Sym) (x y : Bool)
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
    exact owned_intmulcountedstreamreset_safe_left _ (owned_intmulcountedstreamreset_bit_ne_start y)

private theorem owned_intmulcountedstreamreset_reset_left_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) : transition .resetLeft a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, owned_intmulcountedstreamreset_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamreset_reset_right_bit_transition (a : Fin 4 → Sym)
    (hx : a 2 = .zero ∨ a 2 = .one) : transition .resetRight a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos hx]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, owned_intmulcountedstreamreset_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamreset_reset_right_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) (hy : a 3 = .sep) : transition .resetRight a =
      (.halt, fun i => (a i, if i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi]
    apply owned_intmulcountedstreamreset_safe_left
    rcases hi with rfl | rfl
    · rw [hx]; decide
    · rw [hy]; decide
  · simp only [if_neg hi, safe_stay]
/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem owned_intmulcountedstreamreset_tape_replace_after_prefix (M : MultitapeTM)
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



private theorem owned_intmulcountedstreamreset_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamreset_reset_left_read (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
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
    exact owned_intmulcountedstreamreset_reverse_last a xs done
  · change (machine.tapeOf (Sym.sep :: (((b :: ys).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
      (xs.length + 2) = _
    rw [h, show ys.length + 2 = (ys.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    exact owned_intmulcountedstreamreset_reverse_last b ys done

private theorem owned_intmulcountedstreamreset_reset_left_step (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
    (h : xs.length = ys.length) :
    machine.step (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)) =
        resetFrame base .resetLeft (xs.reverse ++ b :: done) (ys.reverse ++ b :: done) (xs.length + 1) := by
  let f := resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done) (xs.length + 2)
  have hx : f.cells 2 (f.head 2) = machine.bitSym a := (owned_intmulcountedstreamreset_reset_left_read base a b xs ys done h).1
  have hy : f.cells 3 (f.head 3) = machine.bitSym b := (owned_intmulcountedstreamreset_reset_left_read base a b xs ys done h).2
  have ht := owned_intmulcountedstreamreset_reset_left_transition (fun i => f.cells i (f.head i)) a b hx hy
  change transition (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).state
    (fun i => (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells i ((resetFrame base .resetLeft ((a :: xs).reverse ++ done)
        ((b :: ys).reverse ++ done) (xs.length + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
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
        owned_intmulcountedstreamreset_tape_replace_after_prefix machine (Sym.sep :: xs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) (machine.bitSym a) (machine.bitSym b)
    · change Function.update (f.cells 3) (f.head 3) (f.cells 3 (f.head 3)) = _
      rw [Function.update_eq_self]
      simp [f, resetFrame, List.reverse_cons, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [resetFrame]

private theorem owned_intmulcountedstreamreset_reset_left_run (base : machine.Cfg) (xs ys done : List Bool) (h : xs.length = ys.length) :
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
          rw [owned_intmulcountedstreamreset_reset_left_step base a b xs ys done ht, ih ys (b :: done) ht]
          simp [List.reverse_cons, List.append_assoc]


private theorem owned_intmulcountedstreamreset_reset_left_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetLeft word word 1) = resetFrame base .resetRight word word 2 := by
  have hs : (resetFrame base .resetLeft word word 1).cells 2
      ((resetFrame base .resetLeft word word 1).head 2) = Sym.sep := rfl
  have ht := owned_intmulcountedstreamreset_reset_left_sep_transition
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) hs
  change transition (resetFrame base .resetLeft word word 1).state
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
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

private theorem owned_intmulcountedstreamreset_reset_right_step (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j < word.length) :
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
  have ht := owned_intmulcountedstreamreset_reset_right_bit_transition
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) hb
  change transition (resetFrame base .resetRight word word (j + 2)).state
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
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

private theorem owned_intmulcountedstreamreset_reset_right_run (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j ≤ word.length) :
    machine.step^[j] (resetFrame base .resetRight word word 2) = resetFrame base .resetRight word word (j + 2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamreset_reset_right_step base word j (by omega)]

private theorem owned_intmulcountedstreamreset_reset_right_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetRight word word (word.length + 2)) =
      resetFrame base .halt word word (word.length + 1) := by
  have hs : (resetFrame base .resetRight word word (word.length + 2)).cells 2
      ((resetFrame base .resetRight word word (word.length + 2)).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: (word.map machine.bitSym ++ [Sym.sep]))) (word.length + 2) = _
    rw [show word.length + 2 = (word.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamreset_reset_right_sep_transition
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) hs hs
  change transition (resetFrame base .resetRight word word (word.length + 2)).state
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
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
private theorem template_reset_correct (base : machine.Cfg) (bits template : List Bool)
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
    have he := owned_intmulcountedstreamreset_reset_left_run base bits.reverse template.reverse [] (by simpa using h)
    simp only [List.length_reverse] at he ⊢
    rw [he]
    simp only [List.reverse_reverse, List.append_nil]
    exact owned_intmulcountedstreamreset_reset_left_end base template
  rw [show 2 * bits.length + 2 = (template.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply, hl, Function.iterate_succ_apply',
    owned_intmulcountedstreamreset_reset_right_run base template template.length le_rfl, owned_intmulcountedstreamreset_reset_right_end]

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem owned_intmulcountedstreamblocks_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamblocks_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamblocks_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private theorem owned_intmulcountedstreamblocks_counter_frame_from_stream (x y old bits : List Bool) (j : ℕ) (q₀ q : State)
    (h : bits.length = y.length) :
    counterFrame (streamFrame x y old j q₀) q bits = streamFrame x y bits j q := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame, h]

private theorem owned_intmulcountedstreamblocks_stream_counter (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step^[counterSteps bits] (streamFrame x y bits j .carry) =
      streamFrame x y (updated bits) j (.done (underflow bits)) := by
  have hf := owned_intmulcountedstreamblocks_counter_frame_from_stream x y bits bits j .carry .carry h
  rw [← hf, counter_correct]
  exact owned_intmulcountedstreamblocks_counter_frame_from_stream x y bits (updated bits) j .carry (.done (underflow bits))
    (by rw [updated_length]; exact h)

private theorem owned_intmulcountedstreamblocks_emit_transition (a : Fin 4 → Sym) (b : Bool)
    (hb : a 0 = machine.bitSym b) (ho : a 1 = .blank) :
    transition .emit a = (.carry, fun i =>
      (if i = 1 then machine.bitSym b else a i, if i = 0 ∨ i = 1 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamblocks_safe_right _
  · change safeStep (a 1) (a 0) .right = (machine.bitSym b, .right)
    rw [ho, hb]
    cases b <;> decide
  · exact safe_stay _
  · exact safe_stay _

private theorem owned_intmulcountedstreamblocks_emit_step (x y bits : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (streamFrame x y bits j .emit) = streamFrame x y bits (j + 1) .carry := by
  have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
  have hr : (streamFrame x y bits j .emit).cells 0 ((streamFrame x y bits j .emit).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have ho : (streamFrame x y bits j .emit).cells 1 ((streamFrame x y bits j .emit).head 1) = Sym.blank := by
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcountedstreamblocks_emit_transition
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) x[j] hr ho
  change transition (streamFrame x y bits j .emit).state
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((streamFrame x y bits j .emit).cells 0) ((streamFrame x y bits j .emit).head 0)
        ((streamFrame x y bits j .emit).cells 0 ((streamFrame x y bits j .emit).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf ((x.take j).map machine.bitSym)) (j + 1)
        (machine.bitSym x[j]) = machine.tapeOf ((x.take (j + 1)).map machine.bitSym)
      have hnew : (x.take (j + 1)).map machine.bitSym =
          (x.take j).map machine.bitSym ++ [machine.bitSym x[j]] := by
        rw [List.take_succ_eq_append_getElem hj, List.map_append]
        rfl
      rw [hnew]
      have hw := owned_intmulcountedstreamblocks_tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
      rw [hl] at hw
      exact hw
    all_goals
      change Function.update ((streamFrame x y bits j .emit).cells _) ((streamFrame x y bits j .emit).head _)
        ((streamFrame x y bits j .emit).cells _ ((streamFrame x y bits j .emit).head _)) = _
      rw [Function.update_eq_self]
      rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [streamFrame]

private theorem owned_intmulcountedstreamblocks_done_transition (a : Fin 4 → Sym) (f : Bool) :
    transition (.done f) a = (if f then .resetLeft else .emit, fun i => (a i, .stay)) := by
  simp [transition, rawTransition, safe_stay]

private theorem owned_intmulcountedstreamblocks_done_false_step (x y bits : List Bool) (j : ℕ) :
    machine.step (streamFrame x y bits j (.done false)) = streamFrame x y bits j .emit := by
  have ht := owned_intmulcountedstreamblocks_done_transition (fun i => (streamFrame x y bits j (.done false)).cells i
    ((streamFrame x y bits j (.done false)).head i)) false
  change transition (streamFrame x y bits j (.done false)).state
    (fun i => (streamFrame x y bits j (.done false)).cells i
      ((streamFrame x y bits j (.done false)).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame x y bits j (.done false)).cells i)
      ((streamFrame x y bits j (.done false)).head i)
      ((streamFrame x y bits j (.done false)).cells i ((streamFrame x y bits j (.done false)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulcountedstreamblocks_done_true_step (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step (streamFrame x y bits j (.done true)) =
      resetFrame (streamFrame x y bits j (.done true)) .resetLeft bits.reverse y (y.length + 1) := by
  have ht := owned_intmulcountedstreamblocks_done_transition (fun i => (streamFrame x y bits j (.done true)).cells i
    ((streamFrame x y bits j (.done true)).head i)) true
  change transition (streamFrame x y bits j (.done true)).state
    (fun i => (streamFrame x y bits j (.done true)).cells i
      ((streamFrame x y bits j (.done true)).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame x y bits j (.done true)).cells i)
      ((streamFrame x y bits j (.done true)).head i)
      ((streamFrame x y bits j (.done true)).cells i ((streamFrame x y bits j (.done true)).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [streamFrame, resetFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [streamFrame, resetFrame]


private theorem owned_intmulcountedstreamblocks_nonterminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hp : 0 < value bits) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      streamFrame x y (updated bits) (j + 1) .emit := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulcountedstreamblocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', owned_intmulcountedstreamblocks_stream_counter x y bits (j + 1) hw,
    (decrement_positive bits hp).1, owned_intmulcountedstreamblocks_done_false_step]

private theorem owned_intmulcountedstreamblocks_loop_run (x y : List Bool) (n : ℕ) (bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hv : n ≤ value bits) (hx : j + n ≤ x.length) :
    machine.step^[2 * n + totalCounterSteps n bits] (streamFrame x y bits j .emit) =
      streamFrame x y (iterateCounter n bits) (j + n) .emit := by
  induction n generalizing bits j with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hval := (decrement_positive bits hp).2
      have htime : 2 * (n + 1) + totalCounterSteps (n + 1) bits =
          (2 * n + totalCounterSteps n (updated bits)) + (counterSteps bits + 2) := by
        rw [totalCounterSteps]
        omega
      rw [htime, Function.iterate_add_apply,
        owned_intmulcountedstreamblocks_nonterminal_cycle x y bits j (by omega) hw hp]
      have hr := ih (updated bits) (j + 1) (by rw [updated_length]; exact hw) (by omega) (by omega)
      simpa only [iterateCounter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private theorem owned_intmulcountedstreamblocks_terminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hz : value bits = 0) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      resetFrame (streamFrame x y (updated bits) (j + 1) (.done true))
        .resetLeft (updated bits).reverse y (y.length + 1) := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulcountedstreamblocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', owned_intmulcountedstreamblocks_stream_counter x y bits (j + 1) hw,
    (underflow_iff_zero bits).mpr hz]
  exact owned_intmulcountedstreamblocks_done_true_step x y (updated bits) (j + 1) (by rw [updated_length]; exact hw)

/-- The last (B-th) emission detects underflow, then takes its actual dispatch
transition into reset. All previous emissions remain in the same finite loop. -/
private theorem owned_intmulcountedstreamblocks_block_run (x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits]
      (streamFrame x y bits j .emit) =
        resetFrame (streamFrame x y last (j + (value bits + 1)) (.done true))
          .resetLeft last.reverse y (y.length + 1) := by
  dsimp only
  have hn : (iterateCounter (value bits) bits).length = y.length := by
    rw [iterate_counter_length]
    exact hw
  have hz : value (iterateCounter (value bits) bits) = 0 := by
    rw [countdown_value bits (value bits) le_rfl]
    omega
  have ht : 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits =
      (counterSteps (iterateCounter (value bits) bits) + 2) +
        (2 * value bits + totalCounterSteps (value bits) bits) := by
    rw [total_counter_steps_succ]
    omega
  rw [ht, Function.iterate_add_apply, owned_intmulcountedstreamblocks_loop_run x y (value bits) bits j hw le_rfl (by omega),
    owned_intmulcountedstreamblocks_terminal_cycle x y (iterateCounter (value bits) bits) (j + value bits) (by omega) hn hz]
  simp only [Nat.add_assoc]

/-- Complete live block, including every payload, counter, dispatch, and reset
transition. The final full configuration also records both returned work heads. -/
private theorem owned_intmulcountedstreamblocks_block_reset_run (x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2)]
      (streamFrame x y bits j .emit) =
        resetFrame (streamFrame x y last (j + (value bits + 1)) (.done true))
          .halt y y (y.length + 1) := by
  dsimp only
  have hl : (updated (iterateCounter (value bits) bits)).reverse.length = y.length := by
    rw [List.length_reverse, updated_length, iterate_counter_length]
    exact hw
  rw [show 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2) =
      (2 * y.length + 2) + (2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits) by omega,
    Function.iterate_add_apply, owned_intmulcountedstreamblocks_block_run x y bits j hw hx]
  have hr := template_reset_correct
    (streamFrame x y (updated (iterateCounter (value bits) bits)) (j + (value bits + 1)) (.done true))
      (updated (iterateCounter (value bits) bits)).reverse y hl
  rw [hl] at hr
  exact hr


private theorem owned_intmulcountedstreamblocks_ready_matches_stream (x y : List Bool) (j : ℕ) (q : State) :
    readyFrame x y j q = streamFrame x y y.reverse j q := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]

private theorem owned_intmulcountedstreamblocks_reset_matches_ready (x y old : List Bool) (j : ℕ) :
    resetFrame (streamFrame x y old j (.done true)) .halt y y (y.length + 1) =
      readyFrame x y j .halt := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]

/-- Initialization is paid only once; the full boundary configuration is public. -/
private theorem setup_ready (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      readyFrame x y 0 .emit := by
  rw [setup_correct, owned_intmulcountedstreamblocks_ready_matches_stream]

/-- One already initialized block returns all physical heads and restores its
descriptor, so a finite caller can reuse it without scanning the whole input. -/
private theorem initialized_block (x y : List Bool) (j : ℕ)
    (hx : j + (IntMul.val y + 1) ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (readyFrame x y j .emit) =
        readyFrame x y (j + (IntMul.val y + 1)) .halt := by
  have hv : value y.reverse = IntMul.val y := by
    change IntMul.BinaryAdder.littleVal y.reverse = IntMul.val y
    rw [← IntMul.BinaryAdder.val_reverse_little, List.reverse_reverse]
  let clock := 2 * (value y.reverse + 1) +
    totalCounterSteps (value y.reverse + 1) y.reverse + (2 * y.length + 2)
  refine ⟨clock, ?_, ?_⟩
  · have hc := total_counter_steps_bound (value y.reverse + 1) y.reverse
    rw [List.length_reverse, hv] at hc
    dsimp only [clock]
    rw [hv]
    omega
  · rw [owned_intmulcountedstreamblocks_ready_matches_stream]
    have hr := owned_intmulcountedstreamblocks_block_reset_run x y y.reverse j (by simp) (by simpa [hv] using hx)
    simpa only [clock, hv, owned_intmulcountedstreamblocks_reset_matches_ready] using hr

private theorem owned_intmulcountedstreamblocks_end_emit_transition (a : Fin 4 → Sym) (h : a 0 = .sep) :
    transition .emit a = (.halt, fun i => (a i,.stay)) := by
  simp [transition, rawTransition, h, safe_stay]

private theorem owned_intmulcountedstreamblocks_end_emit_step (x y bits : List Bool) :
    machine.step (streamFrame x y bits x.length .emit) =
      streamFrame x y bits x.length .halt := by
  have hr : (streamFrame x y bits x.length .emit).cells 0
      ((streamFrame x y bits x.length .emit).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamblocks_end_emit_transition (fun i => (streamFrame x y bits x.length .emit).cells i
    ((streamFrame x y bits x.length .emit).head i)) hr
  change transition (streamFrame x y bits x.length .emit).state
    (fun i => (streamFrame x y bits x.length .emit).cells i
      ((streamFrame x y bits x.length .emit).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulcountedstreamblocks_tail_matches_reset (x y bits : List Bool) (h : bits.length = y.length) :
    streamFrame x y bits x.length .halt =
      resetFrame (readyFrame x y x.length .halt) .halt bits.reverse y (y.length + 1) := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [streamFrame, resetFrame, readyFrame]
  · funext i
    fin_cases i <;> simp [streamFrame, resetFrame, readyFrame, h]

/-- A final short block stops at the input separator. Its counter is left in an
explicit fixed-width frame for the caller's separately charged cleanup. -/
private theorem initialized_tail (x y : List Bool) (j r : ℕ)
    (hr : r ≤ IntMul.val y) (hx : j + r = x.length) :
    ∃ t : ℕ, t ≤ 6 * r + 2 * y.length + 1 ∧
      machine.step^[t] (readyFrame x y j .emit) =
        resetFrame (readyFrame x y x.length .halt) .halt
          (iterateCounter r y.reverse).reverse y (y.length + 1) := by
  have hv : value y.reverse = IntMul.val y := by
    change IntMul.BinaryAdder.littleVal y.reverse = IntMul.val y
    rw [← IntMul.BinaryAdder.val_reverse_little, List.reverse_reverse]
  let clock := 2 * r + totalCounterSteps r y.reverse + 1
  refine ⟨clock, ?_, ?_⟩
  · have hc := total_counter_steps_bound r y.reverse
    rw [List.length_reverse] at hc
    dsimp only [clock]
    omega
  · dsimp only [clock]
    rw [Function.iterate_succ_apply', owned_intmulcountedstreamblocks_ready_matches_stream,
      owned_intmulcountedstreamblocks_loop_run x y r y.reverse j (by simp) (by simpa [hv] using hr) (by omega), hx,
      owned_intmulcountedstreamblocks_end_emit_step, owned_intmulcountedstreamblocks_tail_matches_reset]
    rw [iterate_counter_length]
    simp

end IntMul.CountedStream



namespace IntMul.CountedStream

/-- Full physical frame for the carry step's low-digit prefix routine. -/
private theorem carry_prefix_full (x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 2*x.length+6*(val y+1)+6*y.length+7 ∧
      machine.step^[t] (machine.initCfg x y)=readyFrame x y (val y+1) .halt := by
  obtain ⟨t,ht,he⟩ := initialized_block x y 0 (by simpa using hx)
  refine ⟨t+(2*x.length+2*y.length+5),by omega,?_⟩
  rw [Function.iterate_add_apply,setup_ready,he]
  simp only [Nat.zero_add]

end IntMul.CountedStream



namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem carry_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem owned_intmulcarrystepprograms_safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private theorem owned_intmulcarrystepprograms_safe_adder (q : TapeAdder.State) (a : Fin 3 → Sym) (j : Fin 3) :
    safeStep (a j) ((TapeAdder.machine.δ q a).2 j).1
      ((TapeAdder.machine.δ q a).2 j).2=(TapeAdder.machine.δ q a).2 j := by
  apply owned_intmulcarrystepprograms_safe_identity
  · exact TapeAdder.machine.start_preserved q a j
  · exact TapeAdder.machine.start_only_at_start q a j

private theorem owned_intmulcarrystepprograms_safe_stream (q : CountedStream.State) (a : Fin 4 → Sym) (j : Fin 4) :
    safeStep (a j) ((CountedStream.machine.δ q a).2 j).1
      ((CountedStream.machine.δ q a).2 j).2=(CountedStream.machine.δ q a).2 j := by
  apply owned_intmulcarrystepprograms_safe_identity
  · exact CountedStream.machine.start_preserved q a j
  · exact CountedStream.machine.start_only_at_start q a j

private def adderView (z : List Bool) (c : TapeAdder.machine.Cfg) : subroutine.Cfg where
  state := adderState c.state
  cells := fun i => if i=0 then c.cells 0 else if i=2 then c.cells 1 else if i=3 then c.cells 2
    else if i=4 then subroutine.tapeOf (z.map subroutine.bitSym) else subroutine.tapeOf []
  head := fun i => if i=0 then c.head 0 else if i=2 then c.head 1 else if i=3 then c.head 2 else 0

private def streamView (x y z : List Bool) (c : CountedStream.machine.Cfg) : subroutine.Cfg where
  state := streamState c.state
  cells := fun i =>
    if i=0 then subroutine.tapeOf (x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym)
    else if i=1 then c.cells 1
    else if i=2 then subroutine.tapeOf ((sumWord x y).map subroutine.bitSym)
    else if i=3 then subroutine.tapeOf (x.map subroutine.bitSym)
    else if i=4 then subroutine.tapeOf (z.map subroutine.bitSym)
    else if i=5 then c.cells 0 else if i=6 then c.cells 2 else if i=7 then c.cells 3
    else subroutine.tapeOf []
  head := fun i => if i=0 then x.length+1 else if i=1 then c.head 1
    else if i=2 ∨ i=3 then 0 else if i=4 then z.length+1
    else if i=5 then c.head 0 else if i=6 then c.head 2 else if i=7 then c.head 3 else 0

private theorem adder_step (z : List Bool) (c : TapeAdder.machine.Cfg) :
    subroutine.step (adderView z c)=adderView z (TapeAdder.machine.step c) := by
  let a : Fin 9 → Sym := fun i => (adderView z c).cells i ((adderView z c).head i)
  let b : Fin 3 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (adderTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (adderState c.state) a=
      (adderState (TapeAdder.machine.δ c.state b).1,
        adderAction a (TapeAdder.machine.δ c.state b).2) := by
    by_cases h : c.state=.halt
    · rw [h,TapeAdder.machine.halt_fixed b]
      simp only [adderState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [adderState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact owned_intmulcarrystepprograms_safe_adder c.state b 0
      · exact safe_stay _
      · exact owned_intmulcarrystepprograms_safe_adder c.state b 1
      · exact owned_intmulcarrystepprograms_safe_adder c.state b 2
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
  change transition (adderView z c).state
    (fun i => (adderView z c).cells i ((adderView z c).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rfl
    · exact Function.update_eq_self _ _
    · rfl
    · rfl
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem adder_run (z : List Bool) (c : TapeAdder.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (adderView z c)=adderView z (TapeAdder.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,adder_step,Function.iterate_succ_apply']

private theorem stream_step (x y z : List Bool) (c : CountedStream.machine.Cfg) :
    subroutine.step (streamView x y z c)=streamView x y z (CountedStream.machine.step c) := by
  let a : Fin 9 → Sym := fun i => (streamView x y z c).cells i ((streamView x y z c).head i)
  let b : Fin 4 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (streamTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (streamState c.state) a=
      (streamState (CountedStream.machine.δ c.state b).1,
        streamAction a (CountedStream.machine.δ c.state b).2) := by
    by_cases h : c.state=.halt
    · rw [h,CountedStream.machine.halt_fixed b]
      simp only [streamState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [streamState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_stay _
      · exact owned_intmulcarrystepprograms_safe_stream c.state b 1
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact owned_intmulcarrystepprograms_safe_stream c.state b 0
      · exact owned_intmulcarrystepprograms_safe_stream c.state b 2
      · exact owned_intmulcarrystepprograms_safe_stream c.state b 3
      · exact safe_stay _
  change transition (streamView x y z c).state
    (fun i => (streamView x y z c).cells i ((streamView x y z c).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · rfl
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · rfl
    · rfl
    · rfl
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem stream_run (x y z : List Bool) (c : CountedStream.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (streamView x y z c)=streamView x y z (CountedStream.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,stream_step,Function.iterate_succ_apply']

private theorem carry_initial (x y z : List Bool) :
    initialFrame x y z=FiniteCaller.embed subroutine Phase .add .add dispatch
      (adderView z (TapeAdder.machine.initCfg x y)) := by
  apply carry_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end IntMul.CarryStep



namespace IntMul.CarryStep

open TapeCopy (Sym)

private def inputWord (x y : List Bool) : List Sym :=
  x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym

private def requestWord (x y z : List Bool) : List Sym :=
  (sumWord x y).reverse.map subroutine.bitSym++Sym.sep::z.map subroutine.bitSym

private def transferFrame (x y z : List Bool) (q : Relay) (req : List Sym)
    (h₂ h₄ h₅ : ℕ) : subroutine.Cfg where
  state := relayState q
  cells := fun i => if i=0 then subroutine.tapeOf (inputWord x y)
    else if i=2 then subroutine.tapeOf ((sumWord x y).map subroutine.bitSym)
    else if i=3 then subroutine.tapeOf (x.map subroutine.bitSym)
    else if i=4 then subroutine.tapeOf (z.map subroutine.bitSym)
    else if i=5 then subroutine.tapeOf req else subroutine.tapeOf []
  head := fun i => if i=0 then x.length+1 else if i=2 then h₂
    else if i=4 then h₄ else if i=5 then h₅ else 0

private def seekFrame (x y z : List Bool) (j : ℕ) : subroutine.Cfg :=
  transferFrame x y z .seekSumEnd [] (j+1) 0 0

private def copyFrame (x y z : List Bool) (j : ℕ) : subroutine.Cfg :=
  transferFrame x y z .copySum (((sumWord x y).drop j).reverse.map subroutine.bitSym)
    j 0 ((sumWord x y).length-j+1)

private def descriptorFrame (x y z : List Bool) (j : ℕ) : subroutine.Cfg :=
  transferFrame x y z .copyDescriptor
    ((sumWord x y).reverse.map subroutine.bitSym++Sym.sep::(z.take j).map subroutine.bitSym)
    0 (j+1) ((sumWord x y).length+j+2)

private def rewindFrame (x y z : List Bool) (j : ℕ) : subroutine.Cfg :=
  transferFrame x y z .rewind (requestWord x y z) 0 (z.length+1) j

private def transferFinal (x y z : List Bool) : subroutine.Cfg :=
  {rewindFrame x y z 0 with state := none}

private theorem bit_not_start (b : Bool) : subroutine.bitSym b≠Sym.start := by cases b <;> decide

private theorem bits_read (w : List Bool) (j : ℕ) (hj : j < w.length) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)=subroutine.bitSym w[j] := by
  change (w.map subroutine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem bits_blank (w : List Bool) :
    subroutine.tapeOf (w.map subroutine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map subroutine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem request_read (x y z : List Bool) (j : ℕ) (hj : j < (sumWord x y).length) :
    subroutine.tapeOf (requestWord x y z) (j+1)=
      subroutine.bitSym (((sumWord x y).reverse)[j]'(by simpa using hj)) := by
  change (requestWord x y z).getD j Sym.blank=_
  rw [requestWord,List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem request_sep (x y z : List Bool) :
    subroutine.tapeOf (requestWord x y z) ((sumWord x y).length+1)=Sym.sep := by
  change (requestWord x y z).getD (sumWord x y).length Sym.blank=_
  rw [requestWord,List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem tape_not_start (w : List Sym) (hw : ∀ a ∈ w, a≠Sym.start) (j : ℕ) :
    subroutine.tapeOf w (j+1)≠Sym.start := by
  change w.getD j Sym.blank≠Sym.start
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hw _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem request_not_start (x y z : List Bool) (j : ℕ) (hj : 0 < j) :
    subroutine.tapeOf (requestWord x y z) j≠Sym.start := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  apply tape_not_start
  intro a ha
  simp only [requestWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,hb,rfl⟩|rfl|⟨b,hb,rfl⟩
  · exact bit_not_start b
  · decide
  · exact bit_not_start b

private theorem tape_append_one (w : List Sym) (a : Sym) :
    Function.update (subroutine.tapeOf w) (w.length+1) a=subroutine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p=w.length
    · subst p
      simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1≠w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp;omega)).symm

end IntMul.CarryStep



namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases h : s=Sym.start <;> simp [safeStep,h]

private theorem safe_left (s : Sym) (h : s≠Sym.start) : safeStep s s .left=(s,.left) := by
  simp [safeStep,h]

private theorem seek_step (x y z : List Bool) (j : ℕ) (hj : j < (sumWord x y).length) :
    subroutine.step (seekFrame x y z j)=seekFrame x y z (j+1) := by
  let a : Fin 9 → Sym := fun i => (seekFrame x y z j).cells i ((seekFrame x y z j).head i)
  have hi : a 2=subroutine.bitSym (sumWord x y)[j] := bits_read _ j hj
  have hb : a 2=Sym.zero ∨ a 2=Sym.one := by rw [hi];cases (sumWord x y)[j] <;> decide
  have ht : transition (relayState .seekSumEnd) a=(relayState .seekSumEnd,
      fun i => (a i,if i=2 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_right _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (seekFrame x y z j).state
    (fun i => (seekFrame x y z j).cells i ((seekFrame x y z j).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,transferFrame] <;> omega

private theorem seek_run (x y z : List Bool) (j : ℕ) (hj : j ≤ (sumWord x y).length) :
    subroutine.step^[j] (seekFrame x y z 0)=seekFrame x y z j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),seek_step x y z j (by omega)]

private theorem seek_turn (x y z : List Bool) :
    subroutine.step (seekFrame x y z (sumWord x y).length)=copyFrame x y z (sumWord x y).length := by
  let a : Fin 9 → Sym := fun i => (seekFrame x y z (sumWord x y).length).cells i
    ((seekFrame x y z (sumWord x y).length).head i)
  have hi : a 2=Sym.blank := bits_blank (sumWord x y)
  have ht : transition (relayState .seekSumEnd) a=(relayState .copySum,
      fun i => (a i,if i=2 then Move.left else if i=5 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · simp [hi,safeStep]
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_right _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (seekFrame x y z (sumWord x y).length).state
    (fun i => (seekFrame x y z (sumWord x y).length).cells i
      ((seekFrame x y z (sumWord x y).length).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,copyFrame,transferFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,copyFrame,transferFrame]

private theorem copy_sum_transition (a : Fin 9 → Sym) (b : Bool)
    (hi : a 2=subroutine.bitSym b) (ho : a 5=Sym.blank) :
    transition (relayState .copySum) a=(relayState .copySum,
      fun i => (if i=5 then a 2 else a i,
        if i=2 then Move.left else if i=5 then Move.right else Move.stay)) := by
  have hb : a 2=Sym.zero ∨ a 2=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · cases b <;> simp [hi,safeStep,MultitapeTM.bitSym]
  · exact safe_stay _
  · exact safe_stay _
  · cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _

private theorem copy_sum_step (x y z : List Bool) (j : ℕ) (hj : j+1 ≤ (sumWord x y).length) :
    subroutine.step (copyFrame x y z (j+1))=copyFrame x y z j := by
  let b := (sumWord x y)[j]'(by omega)
  have hi : (copyFrame x y z (j+1)).cells 2 ((copyFrame x y z (j+1)).head 2)=
      subroutine.bitSym b := bits_read _ j (by omega)
  have hl : (((sumWord x y).drop (j+1)).reverse.map subroutine.bitSym).length=
      (sumWord x y).length-(j+1) := by simp
  have ho : (copyFrame x y z (j+1)).cells 5 ((copyFrame x y z (j+1)).head 5)=Sym.blank := by
    change (((sumWord x y).drop (j+1)).reverse.map subroutine.bitSym).getD
      ((sumWord x y).length-(j+1)) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := copy_sum_transition (fun i => (copyFrame x y z (j+1)).cells i
    ((copyFrame x y z (j+1)).head i)) b hi ho
  change transition (copyFrame x y z (j+1)).state
    (fun i => (copyFrame x y z (j+1)).cells i ((copyFrame x y z (j+1)).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf (((sumWord x y).drop (j+1)).reverse.map subroutine.bitSym))
        ((sumWord x y).length-(j+1)+1)
        ((copyFrame x y z (j+1)).cells 2 ((copyFrame x y z (j+1)).head 2))=
          subroutine.tapeOf (((sumWord x y).drop j).reverse.map subroutine.bitSym)
      rw [hi]
      have hd : (sumWord x y).drop j=b::(sumWord x y).drop (j+1) :=
        List.drop_eq_getElem_cons (by omega)
      rw [hd,List.reverse_cons,List.map_append,List.map_singleton]
      have hw := tape_append_one (((sumWord x y).drop (j+1)).reverse.map subroutine.bitSym)
        (subroutine.bitSym b)
      rw [hl] at hw
      exact hw
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyFrame,transferFrame] <;> omega

private theorem copy_sum_run (x y z : List Bool) (j : ℕ) (hj : j ≤ (sumWord x y).length) :
    subroutine.step^[j] (copyFrame x y z j)=copyFrame x y z 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,copy_sum_step x y z j hj,ih (by omega)]

end IntMul.CarryStep



namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem sum_separator_step (x y z : List Bool) :
    subroutine.step (copyFrame x y z 0)=descriptorFrame x y z 0 := by
  let a : Fin 9 → Sym := fun i => (copyFrame x y z 0).cells i ((copyFrame x y z 0).head i)
  have hi : a 2=Sym.start := rfl
  have ho : a 5=Sym.blank := by
    change (((sumWord x y).drop 0).reverse.map subroutine.bitSym).getD
      ((sumWord x y).length-0) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ (by simp)
  have ht : transition (relayState .copySum) a=(relayState .copyDescriptor,
      fun i => (if i=5 then Sym.sep else a i,if i=4 ∨ i=5 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.start=Sym.zero ∨ Sym.start=Sym.one))]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_right _
    · simp [ho,safeStep]
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (copyFrame x y z 0).state
    (fun i => (copyFrame x y z 0).cells i ((copyFrame x y z 0).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf ((sumWord x y).reverse.map subroutine.bitSym))
        ((sumWord x y).length+1) Sym.sep=
          subroutine.tapeOf ((sumWord x y).reverse.map subroutine.bitSym++[Sym.sep])
      simpa only [List.length_map,List.length_reverse] using
        tape_append_one ((sumWord x y).reverse.map subroutine.bitSym) Sym.sep
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyFrame,descriptorFrame,transferFrame] <;> omega

private theorem descriptor_transition (a : Fin 9 → Sym) (b : Bool)
    (hi : a 4=subroutine.bitSym b) (ho : a 5=Sym.blank) :
    transition (relayState .copyDescriptor) a=(relayState .copyDescriptor,
      fun i => (if i=5 then a 4 else a i,if i=4 ∨ i=5 then Move.right else Move.stay)) := by
  have hb : a 4=Sym.zero ∨ a 4=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_right _
  · cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _

private theorem descriptor_step (x y z : List Bool) (j : ℕ) (hj : j < z.length) :
    subroutine.step (descriptorFrame x y z j)=descriptorFrame x y z (j+1) := by
  have hi : (descriptorFrame x y z j).cells 4 ((descriptorFrame x y z j).head 4)=
      subroutine.bitSym z[j] := bits_read z j hj
  let w := (sumWord x y).reverse.map subroutine.bitSym++Sym.sep::(z.take j).map subroutine.bitSym
  have hl : w.length=(sumWord x y).length+j+1 := by simp [w];omega
  have ho : (descriptorFrame x y z j).cells 5 ((descriptorFrame x y z j).head 5)=Sym.blank := by
    change subroutine.tapeOf w ((sumWord x y).length+j+2)=Sym.blank
    rw [show (sumWord x y).length+j+2=((sumWord x y).length+j+1)+1 by omega]
    exact List.getD_eq_default _ _ hl.le
  have ht := descriptor_transition (fun i => (descriptorFrame x y z j).cells i
    ((descriptorFrame x y z j).head i)) z[j] hi ho
  change transition (descriptorFrame x y z j).state
    (fun i => (descriptorFrame x y z j).cells i ((descriptorFrame x y z j).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf w) ((sumWord x y).length+j+2)
        ((descriptorFrame x y z j).cells 4 ((descriptorFrame x y z j).head 4))=
          subroutine.tapeOf ((sumWord x y).reverse.map subroutine.bitSym++
            Sym.sep::(z.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one w (subroutine.bitSym z[j])
      rw [hl,show (sumWord x y).length+j+1+1=(sumWord x y).length+j+2 by omega] at hw
      rw [List.take_succ_eq_append_getElem hj,List.map_append,List.map_singleton]
      simpa only [w,List.append_assoc,List.cons_append] using hw
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [descriptorFrame,transferFrame] <;> omega

private theorem descriptor_run (x y z : List Bool) (j : ℕ) (hj : j ≤ z.length) :
    subroutine.step^[j] (descriptorFrame x y z 0)=descriptorFrame x y z j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),descriptor_step x y z j (by omega)]

private theorem descriptor_rewind_step (x y z : List Bool) :
    subroutine.step (descriptorFrame x y z z.length)=rewindFrame x y z ((sumWord x y).length+z.length+1) := by
  let a : Fin 9 → Sym := fun i => (descriptorFrame x y z z.length).cells i
    ((descriptorFrame x y z z.length).head i)
  have hi : a 4=Sym.blank := bits_blank z
  have ho : a 5≠Sym.start := by
    change subroutine.tapeOf ((sumWord x y).reverse.map subroutine.bitSym++
      Sym.sep::(z.take z.length).map subroutine.bitSym)
        ((sumWord x y).length+z.length+2)≠Sym.start
    simpa only [List.take_length,requestWord] using
      request_not_start x y z ((sumWord x y).length+z.length+2) (by omega)
  have ht : transition (relayState .copyDescriptor) a=(relayState .rewind,
      fun i => (a i,if i=5 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_left _ ho
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (descriptorFrame x y z z.length).state
    (fun i => (descriptorFrame x y z z.length).cells i
      ((descriptorFrame x y z z.length).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [descriptorFrame,rewindFrame,transferFrame,requestWord]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [descriptorFrame,rewindFrame,transferFrame] <;> omega

end IntMul.CarryStep



namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safe_stay)

private theorem rewind_step (x y z : List Bool) (j : ℕ) :
    subroutine.step (rewindFrame x y z (j+1))=rewindFrame x y z j := by
  let a : Fin 9 → Sym := fun i => (rewindFrame x y z (j+1)).cells i
    ((rewindFrame x y z (j+1)).head i)
  have ho : a 5≠Sym.start := request_not_start x y z (j+1) (by omega)
  have ht : transition (relayState .rewind) a=(relayState .rewind,
      fun i => (a i,if i=5 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    rw [if_neg ho]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_left _ ho
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (rewindFrame x y z (j+1)).state
    (fun i => (rewindFrame x y z (j+1)).cells i ((rewindFrame x y z (j+1)).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame,transferFrame]

private theorem rewind_run (x y z : List Bool) (j : ℕ) :
    subroutine.step^[j] (rewindFrame x y z j)=rewindFrame x y z 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem rewind_halt_step (x y z : List Bool) :
    subroutine.step (rewindFrame x y z 0)=transferFinal x y z := by
  let a : Fin 9 → Sym := fun i => (rewindFrame x y z 0).cells i ((rewindFrame x y z 0).head i)
  have ho : a 5=Sym.start := rfl
  have ht : transition (relayState .rewind) a=(none,fun i => (a i,Move.stay)) := by
    simp [transition,rawTransition,relayState,relayRaw,ho,safe_stay]
  change transition (rewindFrame x y z 0).state
    (fun i => (rewindFrame x y z 0).cells i ((rewindFrame x y z 0).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem rewind_complete (x y z : List Bool) (j : ℕ) :
    subroutine.step^[j+1] (rewindFrame x y z j)=transferFinal x y z := by
  rw [Function.iterate_succ_apply',rewind_run,rewind_halt_step]

end IntMul.CarryStep



namespace IntMul.CarryStep

private theorem seek_complete (x y z : List Bool) :
    subroutine.step^[(sumWord x y).length+1] (seekFrame x y z 0)=
      copyFrame x y z (sumWord x y).length := by
  rw [Function.iterate_succ_apply',seek_run x y z _ le_rfl,seek_turn]

private theorem copy_sum_complete (x y z : List Bool) :
    subroutine.step^[(sumWord x y).length+1] (copyFrame x y z (sumWord x y).length)=
      descriptorFrame x y z 0 := by
  rw [Function.iterate_succ_apply',copy_sum_run x y z _ le_rfl,sum_separator_step]

private theorem descriptor_complete (x y z : List Bool) :
    subroutine.step^[z.length+1] (descriptorFrame x y z 0)=
      rewindFrame x y z ((sumWord x y).length+z.length+1) := by
  rw [Function.iterate_succ_apply',descriptor_run x y z z.length le_rfl,descriptor_rewind_step]

private theorem transfer_complete (x y z : List Bool) :
    subroutine.step^[3*(sumWord x y).length+2*z.length+5] (seekFrame x y z 0)=
      transferFinal x y z := by
  have h₂ : subroutine.step^[((sumWord x y).length+1)+((sumWord x y).length+1)]
      (seekFrame x y z 0)=descriptorFrame x y z 0 := by
    rw [Function.iterate_add_apply,seek_complete,copy_sum_complete]
  have h₃ : subroutine.step^[(z.length+1)+(((sumWord x y).length+1)+((sumWord x y).length+1))]
      (seekFrame x y z 0)=rewindFrame x y z ((sumWord x y).length+z.length+1) := by
    rw [Function.iterate_add_apply,h₂,descriptor_complete]
  rw [show 3*(sumWord x y).length+2*z.length+5=
    ((sumWord x y).length+z.length+2)+
      ((z.length+1)+(((sumWord x y).length+1)+((sumWord x y).length+1))) by omega,
    Function.iterate_add_apply,h₃]
  exact rewind_complete x y z ((sumWord x y).length+z.length+1)

private theorem adder_to_transfer (x y z : List Bool) :
    {adderView z (TapeAdder.carrySumFrame x x y (sumWord x y)) with
      state := relayState .seekSumEnd}=seekFrame x y z 0 := by
  apply carry_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [adderView,TapeAdder.carrySumFrame,seekFrame,transferFrame,inputWord] <;> rfl
  · funext i
    fin_cases i <;> simp [adderView,TapeAdder.carrySumFrame,seekFrame,transferFrame]

private theorem transfer_to_prefix (x y z : List Bool) :
    {transferFinal x y z with state := streamState .start}=
      streamView x y z (CountedStream.machine.initCfg (sumWord x y).reverse z) := by
  apply carry_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [transferFinal,rewindFrame,transferFrame,streamView,
      MultitapeTM.initCfg,MultitapeTM.inTape,inputWord,requestWord] <;> rfl
  · funext i
    fin_cases i <;> simp [transferFinal,rewindFrame,transferFrame,streamView,MultitapeTM.initCfg]

end IntMul.CarryStep



namespace IntMul.CarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private def carryCopyFrame (x y z : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .copyCarry
  cells := fun i =>
    if i=0 then subroutine.tapeOf (inputWord x y)
    else if i=1 then subroutine.tapeOf ((digitWord x y z).map subroutine.bitSym)
    else if i=2 then subroutine.tapeOf ((sumWord x y).map subroutine.bitSym)
    else if i=3 then subroutine.tapeOf (x.map subroutine.bitSym)
    else if i=4 then subroutine.tapeOf (z.map subroutine.bitSym)
    else if i=5 then subroutine.tapeOf (requestWord x y z)
    else if i=8 then subroutine.tapeOf (((carryWord x y z).take j).map subroutine.bitSym)
    else subroutine.tapeOf (Sym.sep::(z.map subroutine.bitSym++[Sym.sep]))
  head := fun i => if i=0 then x.length+1 else if i=1 then blockSize z+1
    else if i=2 ∨ i=3 then 0 else if i=5 then blockSize z+j+1
    else if i=8 then j+1 else z.length+1

private def carryOpenFrame (x y z : List Bool) : subroutine.Cfg :=
  {carryCopyFrame x y z 0 with
    state := relayState .openCarry
    head := Function.update (carryCopyFrame x y z 0).head 8 0}

private def carryFinal (x y z : List Bool) : subroutine.Cfg :=
  {carryCopyFrame x y z (carryWord x y z).length with state := none}

private theorem open_carry_step (x y z : List Bool) :
    subroutine.step (carryOpenFrame x y z)=carryCopyFrame x y z 0 := by
  let a : Fin 9 → Sym := fun i => (carryOpenFrame x y z).cells i ((carryOpenFrame x y z).head i)
  have ht : transition (relayState .openCarry) a=(relayState .copyCarry,
      fun i => (a i,if i=8 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_right _
  change transition (carryOpenFrame x y z).state
    (fun i => (carryOpenFrame x y z).cells i ((carryOpenFrame x y z).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [carryOpenFrame,carryCopyFrame]

private theorem carry_copy_transition (a : Fin 9 → Sym) (b : Bool)
    (hi : a 5=subroutine.bitSym b) (ho : a 8=Sym.blank) :
    transition (relayState .copyCarry) a=(relayState .copyCarry,
      fun i => (if i=8 then a 5 else a i,if i=5 ∨ i=8 then Move.right else Move.stay)) := by
  have hb : a 5=Sym.zero ∨ a 5=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_stay _
  · exact safe_right _
  · exact safe_stay _
  · exact safe_stay _
  · cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]

private theorem carry_copy_step (x y z : List Bool) (j : ℕ) (hj : j < (carryWord x y z).length) :
    subroutine.step (carryCopyFrame x y z j)=carryCopyFrame x y z (j+1) := by
  have hsum : blockSize z+j < (sumWord x y).length := by
    simp only [carryWord,List.length_drop,List.length_reverse] at hj
    omega
  have hi : (carryCopyFrame x y z j).cells 5 ((carryCopyFrame x y z j).head 5)=
      subroutine.bitSym (carryWord x y z)[j] := by
    change subroutine.tapeOf (requestWord x y z) (blockSize z+j+1)=_
    rw [request_read x y z (blockSize z+j) hsum]
    simp only [carryWord,List.getElem_drop]
  have hl : (((carryWord x y z).take j).map subroutine.bitSym).length=j := by simp;omega
  have ho : (carryCopyFrame x y z j).cells 8 ((carryCopyFrame x y z j).head 8)=Sym.blank := by
    change (((carryWord x y z).take j).map subroutine.bitSym).getD j Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := carry_copy_transition (fun i => (carryCopyFrame x y z j).cells i
    ((carryCopyFrame x y z j).head i)) (carryWord x y z)[j] hi ho
  change transition (carryCopyFrame x y z j).state
    (fun i => (carryCopyFrame x y z j).cells i ((carryCopyFrame x y z j).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf (((carryWord x y z).take j).map subroutine.bitSym))
        (j+1) ((carryCopyFrame x y z j).cells 5 ((carryCopyFrame x y z j).head 5))=
          subroutine.tapeOf (((carryWord x y z).take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one (((carryWord x y z).take j).map subroutine.bitSym)
        (subroutine.bitSym (carryWord x y z)[j])
      rw [hl] at hw
      rw [List.take_succ_eq_append_getElem hj,List.map_append,List.map_singleton]
      exact hw
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [carryCopyFrame] <;> omega

private theorem carry_copy_run (x y z : List Bool) (j : ℕ) (hj : j ≤ (carryWord x y z).length) :
    subroutine.step^[j] (carryCopyFrame x y z 0)=carryCopyFrame x y z j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),carry_copy_step x y z j (by omega)]

private theorem carry_halt_step (x y z : List Bool) (hB : blockSize z ≤ x.length+1) :
    subroutine.step (carryCopyFrame x y z (carryWord x y z).length)=carryFinal x y z := by
  let a : Fin 9 → Sym := fun i => (carryCopyFrame x y z (carryWord x y z).length).cells i
    ((carryCopyFrame x y z (carryWord x y z).length).head i)
  have hi : a 5=Sym.sep := by
    have he : blockSize z+(carryWord x y z).length+1=(sumWord x y).length+1 := by
      simp only [carryWord,List.length_drop,List.length_reverse,sum_length]
      omega
    change subroutine.tapeOf (requestWord x y z) (blockSize z+(carryWord x y z).length+1)=_
    rw [he,request_sep]
  have ht : transition (relayState .copyCarry) a=(none,fun i => (a i,Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.sep=Sym.zero ∨ Sym.sep=Sym.one))]
    simp only [safe_stay]
  change transition (carryCopyFrame x y z (carryWord x y z).length).state
    (fun i => (carryCopyFrame x y z (carryWord x y z).length).cells i
      ((carryCopyFrame x y z (carryWord x y z).length).head i))=_ at ht
  apply carry_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem carry_copy_complete (x y z : List Bool) (hB : blockSize z ≤ x.length+1) :
    subroutine.step^[(carryWord x y z).length+2] (carryOpenFrame x y z)=carryFinal x y z := by
  have hstart : subroutine.step^[(carryWord x y z).length+1] (carryOpenFrame x y z)=
      carryCopyFrame x y z (carryWord x y z).length := by
    rw [Function.iterate_succ_apply,open_carry_step,carry_copy_run x y z _ le_rfl]
  rw [show (carryWord x y z).length+2=((carryWord x y z).length+1)+1 by omega,
    Function.iterate_succ_apply',hstart,carry_halt_step x y z hB]

end IntMul.CarryStep



namespace IntMul.CarryStep

private theorem owned_intmulcarrystepprimary_after_adder (x y z : List Bool) :
    FiniteCaller.returned subroutine Phase .add .add dispatch
      (adderView z (TapeAdder.carrySumFrame x x y (sumWord x y)))=
    FiniteCaller.embed subroutine Phase .add .transfer dispatch (seekFrame x y z 0) := by
  have h := adder_to_transfer x y z
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply carry_cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem owned_intmulcarrystepprimary_after_transfer (x y z : List Bool) :
    FiniteCaller.returned subroutine Phase .add .transfer dispatch (transferFinal x y z)=
    FiniteCaller.embed subroutine Phase .add .prefix dispatch
      (streamView x y z (CountedStream.machine.initCfg (sumWord x y).reverse z)) := by
  have h := transfer_to_prefix x y z
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply carry_cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem owned_intmulcarrystepprimary_prefix_to_carry (x y z : List Bool) :
    {streamView x y z (CountedStream.readyFrame (sumWord x y).reverse z (blockSize z) .halt)
      with state := relayState .openCarry}=carryOpenFrame x y z := by
  apply carry_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [streamView,CountedStream.readyFrame,carryOpenFrame,carryCopyFrame,
      digitWord,inputWord,requestWord] <;> rfl
  · funext i
    fin_cases i <;> simp [streamView,CountedStream.readyFrame,carryOpenFrame,carryCopyFrame]

private theorem owned_intmulcarrystepprimary_after_prefix (x y z : List Bool) :
    FiniteCaller.returned subroutine Phase .add .prefix dispatch
      (streamView x y z (CountedStream.readyFrame (sumWord x y).reverse z (blockSize z) .halt))=
    FiniteCaller.embed subroutine Phase .add .carry dispatch (carryOpenFrame x y z) := by
  have h := owned_intmulcarrystepprimary_prefix_to_carry x y z
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply carry_cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem owned_intmulcarrystepprimary_after_carry (x y z : List Bool) (hB : blockSize z ≤ x.length+1) :
    FiniteCaller.returned subroutine Phase .add .carry dispatch (carryFinal x y z)=finalFrame x y z := by
  apply carry_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,carryFinal,carryCopyFrame,finalFrame,
      inputWord,requestWord] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,carryFinal,carryCopyFrame,finalFrame,
      carryWord,sum_length] <;> omega

/-- One complete actual local carry step: add equal-width operands, emit the
low digit and physically copy the outgoing carry. The descriptor is already
present in the incoming frame. Every phase and all four returns are charged. -/
private theorem carry_step (x y z : List Bool) (h : x.length=y.length)
    (hB : blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 9*x.length+5*blockSize z+8*z.length+28 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (digitWord x y z).reverse=(val x+val y)%(2^blockSize z) ∧
      val (carryWord x y z).reverse=(val x+val y)/(2^blockSize z) := by
  have ha : subroutine.step^[3*x.length+4] (adderView z (TapeAdder.machine.initCfg x y))=
      adderView z (TapeAdder.carrySumFrame x x y (sumWord x y)) := by
    rw [adder_run,TapeAdder.carry_add_full x y h]
    rfl
  obtain ⟨a,hac,hea⟩ := (FiniteCaller.simulate_run subroutine Phase .add .add dispatch
    (adderView z (TapeAdder.machine.initCfg x y)) (3*x.length+4)).2 (by rw [ha];rfl)
  rw [ha,owned_intmulcarrystepprimary_after_adder] at hea
  obtain ⟨b,hbc,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .add .transfer dispatch
    (seekFrame x y z 0) (3*(sumWord x y).length+2*z.length+5)).2
      (by rw [transfer_complete];rfl)
  rw [transfer_complete,owned_intmulcarrystepprimary_after_transfer] at heb
  obtain ⟨s,hs,hes⟩ := CountedStream.carry_prefix_full (sumWord x y).reverse z
    (by simpa only [List.length_reverse,sum_length,blockSize] using hB)
  have hp : subroutine.step^[s] (streamView x y z (CountedStream.machine.initCfg (sumWord x y).reverse z))=
      streamView x y z (CountedStream.readyFrame (sumWord x y).reverse z (blockSize z) .halt) := by
    rw [stream_run,hes];rfl
  obtain ⟨c,hcc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .add .prefix dispatch
    (streamView x y z (CountedStream.machine.initCfg (sumWord x y).reverse z)) s).2
      (by rw [hp];rfl)
  rw [hp,owned_intmulcarrystepprimary_after_prefix] at hec
  obtain ⟨d,hdc,hed⟩ := (FiniteCaller.simulate_run subroutine Phase .add .carry dispatch
    (carryOpenFrame x y z) ((carryWord x y z).length+2)).2
      (by rw [carry_copy_complete x y z hB];rfl)
  rw [carry_copy_complete x y z hB,owned_intmulcarrystepprimary_after_carry x y z hB] at hed
  have he : machine.step^[d+(c+(b+a))] (initialFrame x y z)=finalFrame x y z := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      carry_initial,hea,heb,hec,hed]
  refine ⟨d+(c+(b+a)),?_,he,?_,(carry_value_split x y z h hB).1,(carry_value_split x y z h hB).2⟩
  · simp only [sum_length,List.length_reverse] at hbc hs
    simp only [carryWord,List.length_drop,List.length_reverse,sum_length] at hdc
    change s ≤ 2*(x.length+1)+6*blockSize z+6*z.length+7 at hs
    omega
  · rw [he];rfl

end IntMul.CarryStep



open IntMul IntMul.CarryStep

theorem solution (x y z : List Bool) (h : x.length=y.length)
    (hB : blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 9*x.length+5*blockSize z+8*z.length+28 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (digitWord x y z).reverse=(val x+val y)%(2^blockSize z) ∧
      val (carryWord x y z).reverse=(val x+val y)/(2^blockSize z) :=
  IntMul.CarryStep.carry_step x y z h hB

#print axioms solution
