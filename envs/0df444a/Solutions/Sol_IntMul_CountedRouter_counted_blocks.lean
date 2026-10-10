-- Prove2me | solution 1 for IntMul.CountedRouter.counted_blocks
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T20:00:02.174915+00:00
-- url     : https://prove2.me/submissions/c15f4a9b-1c42-42b7-86b2-98bb901f252c

import Definitions.Def_IntMul_CountedRouter
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_CountedStream_template_reset_correct
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
private theorem counter_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem counter_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem counter_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem counter_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem counter_carry_zero_transition (a : Fin 4 → Sym) (h : a 2 = .zero) :
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

private theorem counter_carry_one_transition (a : Fin 4 → Sym) (h : a 2 = .one) :
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

private theorem counter_carry_sep_transition (a : Fin 4 → Sym) (h : a 2 = .sep) :
    transition .carry a = (.rewind true, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.sep = Sym.zero),
    if_neg (by decide : ¬Sym.sep = Sym.one)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, counter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem counter_rewind_bit_transition (a : Fin 4 → Sym) (f : Bool)
    (h : a 2 = .zero ∨ a 2 = .one) :
    transition (.rewind f) a = (.rewind f, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, counter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem counter_rewind_sep_transition (a : Fin 4 → Sym) (f : Bool) (h : a 2 = .sep) :
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
    exact counter_safe_left _ (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem counter_bit_mem (b : Bool) : machine.bitSym b = Sym.zero ∨ machine.bitSym b = Sym.one := by
  cases b <;> decide

/-- Reading the least significant remaining bit after the left delimiter. -/
private theorem counter_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem counter_carry_read (base : machine.Cfg) (b : Bool) (bs done : List Bool) :
    (carryFrame base (b :: bs) done).cells 2 ((carryFrame base (b :: bs) done).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
    (bs.length + 2) = machine.bitSym b
  rw [show bs.length + 2 = (bs.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  exact counter_reverse_last b bs done

private theorem counter_carry_zero_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (false :: bs) done) = carryFrame base bs (true :: done) := by
  have hz : (carryFrame base (false :: bs) done).cells 2
      ((carryFrame base (false :: bs) done).head 2) = Sym.zero := counter_carry_read base false bs done
  have ht := counter_carry_zero_transition
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) hz
  change transition (carryFrame base (false :: bs) done).state
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _ at ht
  apply counter_cfg_ext
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
        counter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
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


private theorem counter_carry_one_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (true :: bs) done) = rewindFrame base false (false :: bs).reverse done := by
  have ho : (carryFrame base (true :: bs) done).cells 2
      ((carryFrame base (true :: bs) done).head 2) = Sym.one := counter_carry_read base true bs done
  have ht := counter_carry_one_transition
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) ho
  change transition (carryFrame base (true :: bs) done).state
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _ at ht
  apply counter_cfg_ext
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
        counter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
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

private theorem counter_carry_nil_step (base : machine.Cfg) (done : List Bool) :
    machine.step (carryFrame base [] done) = rewindFrame base true [] done := by
  have hm : (carryFrame base [] done).cells 2 ((carryFrame base [] done).head 2) = Sym.sep := rfl
  have ht := counter_carry_sep_transition
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) hm
  change transition (carryFrame base [] done).state
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _ at ht
  apply counter_cfg_ext
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

private theorem counter_rewind_read (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep])))
    (pre.length + 2) = machine.bitSym b
  rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem counter_rewind_step (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    machine.step (rewindFrame base f pre (b :: bs)) = rewindFrame base f (pre ++ [b]) bs := by
  have hb : (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.zero ∨
      (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.one := by
    rw [counter_rewind_read]
    exact counter_bit_mem b
  have ht := counter_rewind_bit_transition
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) f hb
  change transition (rewindFrame base f pre (b :: bs)).state
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _ at ht
  apply counter_cfg_ext
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

private theorem counter_rewind_end (base : machine.Cfg) (f : Bool) (pre : List Bool) :
    machine.step (rewindFrame base f pre []) = counterFrame base (.done f) pre.reverse := by
  have hs : (rewindFrame base f pre []).cells 2 ((rewindFrame base f pre []).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: ((pre ++ []).map machine.bitSym ++ [Sym.sep])))
      (pre.length + 2) = Sym.sep
    rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ, List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := counter_rewind_sep_transition
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) f hs
  change transition (rewindFrame base f pre []).state
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _ at ht
  apply counter_cfg_ext
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

private theorem counter_rewind_run (base : machine.Cfg) (f : Bool) (pre right : List Bool) :
    machine.step^[right.length + 1] (rewindFrame base f pre right) =
      counterFrame base (.done f) (pre ++ right).reverse := by
  induction right generalizing pre with
  | nil => simpa using counter_rewind_end base f pre
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp,
        Function.iterate_succ_apply, counter_rewind_step, ih]
      simp [List.append_assoc]

private theorem counter_carry_run (base : machine.Cfg) (bits done : List Bool) :
    machine.step^[carryLength bits + 1] (carryFrame base bits done) =
      rewindFrame base (underflow bits) (stopTail bits).reverse
        (List.replicate (carryLength bits) true ++ done) := by
  induction bits generalizing done with
  | nil => simpa [carryLength, underflow, stopTail] using counter_carry_nil_step base done
  | cons b bs ih =>
      cases b
      · simp only [carryLength, underflow, stopTail, if_true]
        rw [Function.iterate_succ_apply, counter_carry_zero_step, ih]
        simp [List.replicate_succ', List.append_assoc]
      · simpa [carryLength, underflow, stopTail] using counter_carry_one_step base bs done

/-- The actual decrement table restores the head and preserves all other tapes.
Its exact count includes propagation, resolution, and the full head return. -/
private theorem counter_correct (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits) =
      counterFrame base (.done (underflow bits)) (updated bits) := by
  have hc : counterFrame base .carry bits = carryFrame base bits [] := by
    apply counter_cfg_ext <;> simp [counterFrame, carryFrame]
  have ht : counterSteps bits = (carryLength bits + 1) + (carryLength bits + 1) := by
    unfold counterSteps
    omega
  rw [hc, ht, Function.iterate_add_apply, counter_carry_run]
  simp only [List.append_nil]
  have hr := counter_rewind_run base (underflow bits) (stopTail bits).reverse (List.replicate (carryLength bits) true)
  simpa [updated, List.reverse_append, List.reverse_replicate] using hr

end IntMul.CountedStream




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

private def setup_scanXFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .scanX
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym) else machine.tapeOf []
  head := fun i => if i = 0 then j + 1 else 1

private def setup_copyYFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyY
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2 + j else if i = 2 ∨ i = 3 then j + 2 else 1

private def setup_rewindInputFrame (x y : List Bool) (p : ℕ) : machine.Cfg where
  state := .rewindInput
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
    else machine.tapeOf []
  head := fun i => if i = 0 then p else if i = 2 ∨ i = 3 then y.length + 1 else 1

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

private theorem setup_initial_transition (a : Fin 4 → Sym) :
    transition .start a = (.scanX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, setup_safe_right]

private theorem setup_setup_start (x y : List Bool) :
    machine.step (machine.initCfg x y) = setup_scanXFrame x y 0 := by
  have ht := setup_initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply setup_cfg_ext
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

private theorem setup_scan_bit_transition (a : Fin 4 → Sym)
    (h : a 0 = .zero ∨ a 0 = .one) :
    transition .scanX a = (.scanX, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, setup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem setup_scan_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (setup_scanXFrame x y j) = setup_scanXFrame x y (j + 1) := by
  have hr : (setup_scanXFrame x y j).cells 0 ((setup_scanXFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (setup_scanXFrame x y j).cells 0 ((setup_scanXFrame x y j).head 0) = Sym.zero ∨
      (setup_scanXFrame x y j).cells 0 ((setup_scanXFrame x y j).head 0) = Sym.one := by
    rw [hr]
    cases x[j] <;> decide
  have ht := setup_scan_bit_transition
    (fun i => (setup_scanXFrame x y j).cells i ((setup_scanXFrame x y j).head i)) hb
  change transition (setup_scanXFrame x y j).state
    (fun i => (setup_scanXFrame x y j).cells i ((setup_scanXFrame x y j).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((setup_scanXFrame x y j).cells i) ((setup_scanXFrame x y j).head i)
      ((setup_scanXFrame x y j).cells i ((setup_scanXFrame x y j).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [setup_scanXFrame, hi]

private theorem setup_scan_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = setup_scanXFrame x y j := by
  induction j with
  | zero => simpa using setup_setup_start x y
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), setup_scan_step x y j (by omega)]


private theorem setup_scan_end_transition (a : Fin 4 → Sym) (hs : a 0 = .sep)
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
    exact setup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .right = (Sym.sep, .right)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .right = (Sym.sep, .right)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem setup_scan_end (x y : List Bool) :
    machine.step (setup_scanXFrame x y x.length) = setup_copyYFrame x y 0 := by
  have hs : (setup_scanXFrame x y x.length).cells 0 ((setup_scanXFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (setup_scanXFrame x y x.length).cells i ((setup_scanXFrame x y x.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp [setup_scanXFrame, h0, MultitapeTM.tapeOf]
  have ht := setup_scan_end_transition
    (fun i => (setup_scanXFrame x y x.length).cells i ((setup_scanXFrame x y x.length).head i)) hs hw
  change transition (setup_scanXFrame x y x.length).state
    (fun i => (setup_scanXFrame x y x.length).cells i ((setup_scanXFrame x y x.length).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((setup_scanXFrame x y x.length).cells 0) ((setup_scanXFrame x y x.length).head 0)
        ((setup_scanXFrame x y x.length).cells 0 ((setup_scanXFrame x y x.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf []) 1 Sym.sep = machine.tapeOf [Sym.sep]
      exact setup_tapeOf_append_one machine [] Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [setup_scanXFrame, setup_copyYFrame]

private theorem setup_copy_bit_transition (a : Fin 4 → Sym) (b : Bool) (hb : a 0 = machine.bitSym b)
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
    exact setup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 2 (Or.inl rfl), hb]
    cases b <;> decide
  · change safeStep (a 3) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 3 (Or.inr rfl), hb]
    cases b <;> decide

private theorem setup_copy_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (setup_copyYFrame x y j) = setup_copyYFrame x y (j + 1) := by
  have hl : (Sym.sep :: (y.take j).map machine.bitSym).length = j + 1 := by
    simp [Nat.min_eq_left hj.le]
  have hr : (setup_copyYFrame x y j).cells 0 ((setup_copyYFrame x y j).head 0) = machine.bitSym y[j] := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)) (x.length + 2 + j) = _
    rw [show x.length + 2 + j = (x.length + 1 + j) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show x.length + 1 + j - x.length = j + 1 by omega, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (setup_copyYFrame x y j).cells i ((setup_copyYFrame x y j).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [setup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take j).map machine.bitSym).getD (j + 1) machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := setup_copy_bit_transition
    (fun i => (setup_copyYFrame x y j).cells i ((setup_copyYFrame x y j).head i)) y[j] hr hw
  change transition (setup_copyYFrame x y j).state
    (fun i => (setup_copyYFrame x y j).cells i ((setup_copyYFrame x y j).head i)) = _ at ht
  have hnew : Sym.sep :: (y.take (j + 1)).map machine.bitSym =
      (Sym.sep :: (y.take j).map machine.bitSym) ++ [machine.bitSym y[j]] := by
    rw [List.take_succ_eq_append_getElem hj, List.map_append]
    rfl
  have hwrite := setup_tapeOf_append_one machine (Sym.sep :: (y.take j).map machine.bitSym) (machine.bitSym y[j])
  rw [hl] at hwrite
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((setup_copyYFrame x y j).cells 0) ((setup_copyYFrame x y j).head 0)
        ((setup_copyYFrame x y j).cells 0 ((setup_copyYFrame x y j).head 0)) = _
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
    fin_cases i <;> simp [setup_copyYFrame] <;> omega

private theorem setup_copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (setup_copyYFrame x y 0) = setup_copyYFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), setup_copy_step x y j (by omega)]


private theorem setup_copy_end_transition (a : Fin 4 → Sym) (hs : a 0 = .blank)
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
    exact setup_safe_left _ (by decide)
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .left = (Sym.sep, .left)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .left = (Sym.sep, .left)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem setup_copy_end (x y : List Bool) :
    machine.step (setup_copyYFrame x y y.length) = setup_rewindInputFrame x y (x.length + y.length + 1) := by
  have hs : (setup_copyYFrame x y y.length).cells 0 ((setup_copyYFrame x y y.length).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym))
      (x.length + 2 + y.length) = _
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    exact List.getD_eq_default _ _ (by simp; omega)
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (setup_copyYFrame x y y.length).cells i ((setup_copyYFrame x y y.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [setup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take y.length).map machine.bitSym).getD (y.length + 1) machine.blank = _
    rw [List.take_length]
    exact List.getD_eq_default _ _ (by simp)
  have ht := setup_copy_end_transition
    (fun i => (setup_copyYFrame x y y.length).cells i ((setup_copyYFrame x y y.length).head i)) hs hw
  change transition (setup_copyYFrame x y y.length).state
    (fun i => (setup_copyYFrame x y y.length).cells i ((setup_copyYFrame x y y.length).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((setup_copyYFrame x y y.length).cells 0) ((setup_copyYFrame x y y.length).head 0)
        ((setup_copyYFrame x y y.length).cells 0 ((setup_copyYFrame x y y.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf (Sym.sep :: (y.take y.length).map machine.bitSym))
        (y.length + 2) Sym.sep = machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
      simpa [List.take_length] using setup_tapeOf_append_one machine (Sym.sep :: y.map machine.bitSym) Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [setup_copyYFrame, setup_rewindInputFrame] <;> omega

private theorem setup_input_getD_ne_start (x y : List Bool) (p : ℕ) :
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

private theorem setup_rewind_transition (a : Fin 4 → Sym) (h : a 0 ≠ .start) :
    transition .rewindInput a = (.rewindInput, fun i => (a i, if i = 0 then .left else .stay)) := by
  simp only [transition, rawTransition, if_neg h]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    exact setup_safe_left _ h
  · simp only [if_neg hi, safe_stay]

private theorem setup_rewind_step (x y : List Bool) (p : ℕ) :
    machine.step (setup_rewindInputFrame x y (p + 1)) = setup_rewindInputFrame x y p := by
  have hn : (setup_rewindInputFrame x y (p + 1)).cells 0 ((setup_rewindInputFrame x y (p + 1)).head 0) ≠ Sym.start :=
    setup_input_getD_ne_start x y p
  have ht := setup_rewind_transition
    (fun i => (setup_rewindInputFrame x y (p + 1)).cells i ((setup_rewindInputFrame x y (p + 1)).head i)) hn
  change transition (setup_rewindInputFrame x y (p + 1)).state
    (fun i => (setup_rewindInputFrame x y (p + 1)).cells i ((setup_rewindInputFrame x y (p + 1)).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((setup_rewindInputFrame x y (p + 1)).cells i) ((setup_rewindInputFrame x y (p + 1)).head i)
      ((setup_rewindInputFrame x y (p + 1)).cells i ((setup_rewindInputFrame x y (p + 1)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [setup_rewindInputFrame, hi]

private theorem setup_rewind_run (x y : List Bool) (p : ℕ) :
    machine.step^[p] (setup_rewindInputFrame x y p) = setup_rewindInputFrame x y 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply, setup_rewind_step, ih]

private theorem setup_rewind_end_transition (a : Fin 4 → Sym) (h : a 0 = .start) :
    transition .rewindInput a = (.emit, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, setup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem setup_rewind_end (x y : List Bool) :
    machine.step (setup_rewindInputFrame x y 0) = streamFrame x y y.reverse 0 .emit := by
  have hs : (setup_rewindInputFrame x y 0).cells 0 ((setup_rewindInputFrame x y 0).head 0) = Sym.start := rfl
  have ht := setup_rewind_end_transition
    (fun i => (setup_rewindInputFrame x y 0).cells i ((setup_rewindInputFrame x y 0).head i)) hs
  change transition (setup_rewindInputFrame x y 0).state
    (fun i => (setup_rewindInputFrame x y 0).cells i ((setup_rewindInputFrame x y 0).head i)) = _ at ht
  apply setup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((setup_rewindInputFrame x y 0).cells i) ((setup_rewindInputFrame x y 0).head i)
      ((setup_rewindInputFrame x y 0).cells i ((setup_rewindInputFrame x y 0).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [setup_rewindInputFrame, streamFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [setup_rewindInputFrame, streamFrame]

/-- Exact setup cost includes both operand/descriptor scans, the saved copy,
separator writes, and the input-head return to the first payload bit. -/
private theorem setup_correct (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      streamFrame x y y.reverse 0 .emit := by
  have hscan : machine.step^[x.length + 2] (machine.initCfg x y) = setup_copyYFrame x y 0 := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply', setup_scan_run x y x.length le_rfl, setup_scan_end]
  have hcopy : machine.step^[x.length + y.length + 3] (machine.initCfg x y) =
      setup_rewindInputFrame x y (x.length + y.length + 1) := by
    rw [show x.length + y.length + 3 = (y.length + (x.length + 2)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hscan,
      setup_copy_run x y y.length le_rfl, setup_copy_end]
  rw [show 2 * x.length + 2 * y.length + 5 =
      ((x.length + y.length + 1) + (x.length + y.length + 3)) + 1 by omega,
    Function.iterate_succ_apply', Function.iterate_add_apply, hcopy, setup_rewind_run, setup_rewind_end]

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem blocks_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem blocks_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem blocks_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private theorem blocks_counter_frame_from_stream (x y old bits : List Bool) (j : ℕ) (q₀ q : State)
    (h : bits.length = y.length) :
    counterFrame (streamFrame x y old j q₀) q bits = streamFrame x y bits j q := by
  apply blocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame, h]

private theorem blocks_stream_counter (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step^[counterSteps bits] (streamFrame x y bits j .carry) =
      streamFrame x y (updated bits) j (.done (underflow bits)) := by
  have hf := blocks_counter_frame_from_stream x y bits bits j .carry .carry h
  rw [← hf, counter_correct]
  exact blocks_counter_frame_from_stream x y bits (updated bits) j .carry (.done (underflow bits))
    (by rw [updated_length]; exact h)

private theorem blocks_emit_transition (a : Fin 4 → Sym) (b : Bool)
    (hb : a 0 = machine.bitSym b) (ho : a 1 = .blank) :
    transition .emit a = (.carry, fun i =>
      (if i = 1 then machine.bitSym b else a i, if i = 0 ∨ i = 1 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact blocks_safe_right _
  · change safeStep (a 1) (a 0) .right = (machine.bitSym b, .right)
    rw [ho, hb]
    cases b <;> decide
  · exact safe_stay _
  · exact safe_stay _

private theorem blocks_emit_step (x y bits : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (streamFrame x y bits j .emit) = streamFrame x y bits (j + 1) .carry := by
  have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
  have hr : (streamFrame x y bits j .emit).cells 0 ((streamFrame x y bits j .emit).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have ho : (streamFrame x y bits j .emit).cells 1 ((streamFrame x y bits j .emit).head 1) = Sym.blank := by
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := blocks_emit_transition
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) x[j] hr ho
  change transition (streamFrame x y bits j .emit).state
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) = _ at ht
  apply blocks_cfg_ext
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
      have hw := blocks_tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
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

private theorem blocks_done_transition (a : Fin 4 → Sym) (f : Bool) :
    transition (.done f) a = (if f then .resetLeft else .emit, fun i => (a i, .stay)) := by
  simp [transition, rawTransition, safe_stay]

private theorem blocks_done_false_step (x y bits : List Bool) (j : ℕ) :
    machine.step (streamFrame x y bits j (.done false)) = streamFrame x y bits j .emit := by
  have ht := blocks_done_transition (fun i => (streamFrame x y bits j (.done false)).cells i
    ((streamFrame x y bits j (.done false)).head i)) false
  change transition (streamFrame x y bits j (.done false)).state
    (fun i => (streamFrame x y bits j (.done false)).cells i
      ((streamFrame x y bits j (.done false)).head i)) = _ at ht
  apply blocks_cfg_ext
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

private theorem blocks_done_true_step (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step (streamFrame x y bits j (.done true)) =
      resetFrame (streamFrame x y bits j (.done true)) .resetLeft bits.reverse y (y.length + 1) := by
  have ht := blocks_done_transition (fun i => (streamFrame x y bits j (.done true)).cells i
    ((streamFrame x y bits j (.done true)).head i)) true
  change transition (streamFrame x y bits j (.done true)).state
    (fun i => (streamFrame x y bits j (.done true)).cells i
      ((streamFrame x y bits j (.done true)).head i)) = _ at ht
  apply blocks_cfg_ext
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


private theorem blocks_nonterminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hp : 0 < value bits) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      streamFrame x y (updated bits) (j + 1) .emit := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, blocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', blocks_stream_counter x y bits (j + 1) hw,
    (decrement_positive bits hp).1, blocks_done_false_step]

private theorem blocks_loop_run (x y : List Bool) (n : ℕ) (bits : List Bool) (j : ℕ)
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
        blocks_nonterminal_cycle x y bits j (by omega) hw hp]
      have hr := ih (updated bits) (j + 1) (by rw [updated_length]; exact hw) (by omega) (by omega)
      simpa only [iterateCounter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private theorem blocks_terminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hz : value bits = 0) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      resetFrame (streamFrame x y (updated bits) (j + 1) (.done true))
        .resetLeft (updated bits).reverse y (y.length + 1) := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, blocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', blocks_stream_counter x y bits (j + 1) hw,
    (underflow_iff_zero bits).mpr hz]
  exact blocks_done_true_step x y (updated bits) (j + 1) (by rw [updated_length]; exact hw)

/-- The last (B-th) emission detects underflow, then takes its actual dispatch
transition into reset. All previous emissions remain in the same finite loop. -/
private theorem blocks_block_run (x y bits : List Bool) (j : ℕ)
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
  rw [ht, Function.iterate_add_apply, blocks_loop_run x y (value bits) bits j hw le_rfl (by omega),
    blocks_terminal_cycle x y (iterateCounter (value bits) bits) (j + value bits) (by omega) hn hz]
  simp only [Nat.add_assoc]

/-- Complete live block, including every payload, counter, dispatch, and reset
transition. The final full configuration also records both returned work heads. -/
private theorem blocks_block_reset_run (x y bits : List Bool) (j : ℕ)
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
    Function.iterate_add_apply, blocks_block_run x y bits j hw hx]
  have hr := template_reset_correct
    (streamFrame x y (updated (iterateCounter (value bits) bits)) (j + (value bits + 1)) (.done true))
      (updated (iterateCounter (value bits) bits)).reverse y hl
  rw [hl] at hr
  exact hr


private theorem blocks_ready_matches_stream (x y : List Bool) (j : ℕ) (q : State) :
    readyFrame x y j q = streamFrame x y y.reverse j q := by
  apply blocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]

private theorem blocks_reset_matches_ready (x y old : List Bool) (j : ℕ) :
    resetFrame (streamFrame x y old j (.done true)) .halt y y (y.length + 1) =
      readyFrame x y j .halt := by
  apply blocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]

/-- Initialization is paid only once; the full boundary configuration is public. -/
private theorem setup_ready (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      readyFrame x y 0 .emit := by
  rw [setup_correct, blocks_ready_matches_stream]

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
  · rw [blocks_ready_matches_stream]
    have hr := blocks_block_reset_run x y y.reverse j (by simp) (by simpa [hv] using hx)
    simpa only [clock, hv, blocks_reset_matches_ready] using hr

private theorem blocks_end_emit_transition (a : Fin 4 → Sym) (h : a 0 = .sep) :
    transition .emit a = (.halt, fun i => (a i,.stay)) := by
  simp [transition, rawTransition, h, safe_stay]

private theorem blocks_end_emit_step (x y bits : List Bool) :
    machine.step (streamFrame x y bits x.length .emit) =
      streamFrame x y bits x.length .halt := by
  have hr : (streamFrame x y bits x.length .emit).cells 0
      ((streamFrame x y bits x.length .emit).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := blocks_end_emit_transition (fun i => (streamFrame x y bits x.length .emit).cells i
    ((streamFrame x y bits x.length .emit).head i)) hr
  change transition (streamFrame x y bits x.length .emit).state
    (fun i => (streamFrame x y bits x.length .emit).cells i
      ((streamFrame x y bits x.length .emit).head i)) = _ at ht
  apply blocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem blocks_tail_matches_reset (x y bits : List Bool) (h : bits.length = y.length) :
    streamFrame x y bits x.length .halt =
      resetFrame (readyFrame x y x.length .halt) .halt bits.reverse y (y.length + 1) := by
  apply blocks_cfg_ext
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
    rw [Function.iterate_succ_apply', blocks_ready_matches_stream,
      blocks_loop_run x y r y.reverse j (by simp) (by simpa [hv] using hr) (by omega), hx,
      blocks_end_emit_step, blocks_tail_matches_reset]
    rw [iterate_counter_length]
    simp

end IntMul.CountedStream



namespace IntMul.CountedRouter

open IntMul.TapeCopy (Sym)

private abbrev router_subroutine : MultitapeTM := CountedStream.machine
private abbrev router_lift (e : Bool) (c : router_subroutine.Cfg) : machine.Cfg :=
  FiniteCaller.embed router_subroutine Bool false e dispatch c
private abbrev router_after (e : Bool) (c : router_subroutine.Cfg) : machine.Cfg :=
  FiniteCaller.returned router_subroutine Bool false e dispatch c
private abbrev router_blockSize (y : List Bool) : ℕ := IntMul.val y + 1
private abbrev router_blockCost (y : List Bool) : ℕ := 6 * router_blockSize y + 4 * y.length + 3

private theorem router_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem router_call (e : Bool) (c : router_subroutine.Cfg) (T : ℕ)
    (h : (router_subroutine.step^[T] c).state = router_subroutine.qHalt) :
    ∃ t : ℕ, t ≤ T + 1 ∧ machine.step^[t] (router_lift e c) = router_after e (router_subroutine.step^[T] c) :=
  (FiniteCaller.simulate_run router_subroutine Bool false e dispatch c T).2 h

private theorem router_segment (e : Bool) (c : router_subroutine.Cfg) (T : ℕ)
    (h : (router_subroutine.step^[T] c).state ≠ router_subroutine.qHalt) :
    machine.step^[T] (router_lift e c) = router_lift e (router_subroutine.step^[T] c) :=
  (FiniteCaller.simulate_run router_subroutine Bool false e dispatch c T).1 h

private theorem router_ready_read (x y : List Bool) (j : ℕ) (q : CountedStream.State)
    (hj : j < x.length) :
    (CountedStream.readyFrame x y j q).cells 0
      ((CountedStream.readyFrame x y j q).head 0) = router_subroutine.bitSym x[j] := by
  change (x.map router_subroutine.bitSym ++ Sym.sep :: y.map router_subroutine.bitSym).getD j router_subroutine.blank = _
  rw [List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

private theorem router_ready_read_end (x y : List Bool) (q : CountedStream.State) :
    (CountedStream.readyFrame x y x.length q).cells 0
      ((CountedStream.readyFrame x y x.length q).head 0) = Sym.sep := by
  change (x.map router_subroutine.bitSym ++ Sym.sep :: y.map router_subroutine.bitSym).getD x.length router_subroutine.blank = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem router_after_live (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    router_after false (CountedStream.readyFrame x y j .halt) =
      router_lift false (CountedStream.readyFrame x y j .emit) := by
  apply router_cfg_ext
  · change dispatch false (fun i => (CountedStream.readyFrame x y j .halt).cells i
      ((CountedStream.readyFrame x y j .halt).head i)) = some (false,CountedStream.State.emit)
    simp only [dispatch, Bool.false_eq_true, ↓reduceIte]
    simp only [router_ready_read x y j .halt hj]
    cases x[j] <;> decide
  · rfl
  · rfl

private theorem router_after_end (c : router_subroutine.Cfg)
    (h : c.cells 0 (c.head 0) = Sym.sep) :
    router_after false c = router_lift true {c with state := .resetLeft} := by
  apply router_cfg_ext
  · change dispatch false (fun i => c.cells i (c.head i)) = some (true,CountedStream.State.resetLeft)
    simp [dispatch, h]
  · rfl
  · rfl

private theorem router_ready_reset_eq (x y : List Bool) (j : ℕ) :
    CountedStream.resetFrame (CountedStream.readyFrame x y j .halt)
      .halt y y (y.length + 1) = CountedStream.readyFrame x y j .halt := by
  apply router_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame, CountedStream.readyFrame]
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame, CountedStream.readyFrame]

private theorem router_ready_as_reset (x y : List Bool) (j : ℕ) :
    CountedStream.readyFrame x y j .resetLeft =
      CountedStream.resetFrame (CountedStream.readyFrame x y j .halt)
        .resetLeft y y (y.length + 1) := by
  apply router_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame, CountedStream.readyFrame]
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame, CountedStream.readyFrame]

private theorem router_after_cleanup (x y : List Bool) (j : ℕ) :
    router_after true (CountedStream.readyFrame x y j .halt) = frame x y j none := by
  rfl

/-- Cleanup is an actual router_subroutine run and a charged return transition. -/
private theorem router_cleanup (x y bits : List Bool) (h : bits.length = y.length) :
    ∃ t : ℕ, t ≤ 2 * y.length + 3 ∧
      machine.step^[t]
        (router_lift true (CountedStream.resetFrame (CountedStream.readyFrame x y x.length .halt)
          .resetLeft bits y (y.length + 1))) = frame x y x.length none := by
  have hr := CountedStream.template_reset_correct
    (CountedStream.readyFrame x y x.length .halt) bits y h
  rw [h, router_ready_reset_eq] at hr
  obtain ⟨t,ht,he⟩ := router_call true _ (2 * y.length + 2) (by rw [hr]; rfl)
  refine ⟨t, by omega, ?_⟩
  rw [hr, router_after_cleanup] at he
  exact he

/-- Every nonfinal full block returns to its ready boundary in the same literal
machine. No router_setup scans or free head changes occur between blocks. -/
private theorem router_full_blocks (x y : List Bool) (q j : ℕ)
    (hx : j + q * router_blockSize y < x.length) :
    ∃ t : ℕ, t ≤ q * router_blockCost y ∧
      machine.step^[t] (router_lift false (CountedStream.readyFrame x y j .emit)) =
        router_lift false (CountedStream.readyFrame x y (j + q * router_blockSize y) .emit) := by
  induction q generalizing j with
  | zero => refine ⟨0, by simp, ?_⟩; simp
  | succ q ih =>
      have hx' : j + router_blockSize y + q * router_blockSize y < x.length := by
        rw [Nat.succ_mul] at hx
        omega
      have hj : j + router_blockSize y < x.length := by omega
      obtain ⟨T,hT,hM⟩ := CountedStream.initialized_block x y j
        (by simpa only [router_blockSize] using hj.le)
      obtain ⟨u,hu,he⟩ := router_call false _ T (by rw [hM]; rfl)
      rw [hM, router_after_live x y (j + router_blockSize y) hj] at he
      obtain ⟨v,hv,hr⟩ := ih (j + router_blockSize y) hx'
      refine ⟨v + u, ?_, ?_⟩
      · change v + u ≤ (q + 1) * (6 * (IntMul.val y + 1) + 4 * y.length + 3)
        rw [Nat.succ_mul]
        dsimp only [router_blockCost, router_blockSize] at hv
        omega
      · rw [Function.iterate_add_apply, he, hr]
        congr 2
        rw [Nat.succ_mul]
        omega

/-- The final block may be full, short, or empty. A short block reaches the
input delimiter, then the caller runs saved-template router_cleanup before halting. -/
private theorem router_last_block (x y : List Bool) (j r : ℕ)
    (hr : r ≤ router_blockSize y) (hx : j + r = x.length) :
    ∃ t : ℕ, t ≤ 6 * r + 6 * y.length + 6 ∧
      machine.step^[t] (router_lift false (CountedStream.readyFrame x y j .emit)) =
        frame x y x.length none := by
  by_cases hfull : r = router_blockSize y
  · have hj : j + router_blockSize y = x.length := by omega
    obtain ⟨T,hT,hM⟩ := CountedStream.initialized_block x y j
      (by simpa only [router_blockSize] using hj.le)
    rw [hj] at hM
    obtain ⟨u,hu,he⟩ := router_call false _ T (by rw [hM]; rfl)
    rw [hM, router_after_end _ (router_ready_read_end x y .halt)] at he
    change machine.step^[u] (router_lift false (CountedStream.readyFrame x y j .emit)) =
      router_lift true (CountedStream.readyFrame x y x.length .resetLeft) at he
    rw [router_ready_as_reset] at he
    obtain ⟨v,hv,hc⟩ := router_cleanup x y y rfl
    refine ⟨v + u, ?_, ?_⟩
    · dsimp only [router_blockSize] at hfull
      omega
    · rw [Function.iterate_add_apply, he, hc]
  · have hsmall : r ≤ IntMul.val y := by dsimp only [router_blockSize] at hr hfull; omega
    obtain ⟨T,hT,hM⟩ := CountedStream.initialized_tail x y j r hsmall hx
    let bits := (CountedStream.iterateCounter r y.reverse).reverse
    have hw : bits.length = y.length := by
      dsimp only [bits]
      rw [List.length_reverse, CountedStream.iterate_counter_length, List.length_reverse]
    obtain ⟨u,hu,he⟩ := router_call false _ T (by rw [hM]; rfl)
    rw [hM, router_after_end _ (by simpa [CountedStream.resetFrame] using router_ready_read_end x y .halt)] at he
    change machine.step^[u] (router_lift false (CountedStream.readyFrame x y j .emit)) =
      router_lift true (CountedStream.resetFrame (CountedStream.readyFrame x y x.length .halt)
        .resetLeft bits y (y.length + 1)) at he
    obtain ⟨v,hv,hc⟩ := router_cleanup x y bits hw
    refine ⟨v + u, by omega, ?_⟩
    rw [Function.iterate_add_apply, he, hc]

private theorem router_setup (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      router_lift false (CountedStream.readyFrame x y 0 .emit) := by
  have hi : machine.initCfg x y = router_lift false (router_subroutine.initCfg x y) := by rfl
  have hn : (router_subroutine.step^[2 * x.length + 2 * y.length + 5]
      (router_subroutine.initCfg x y)).state ≠ router_subroutine.qHalt := by
    rw [CountedStream.setup_ready]
    change CountedStream.State.emit ≠ CountedStream.State.halt
    decide
  rw [hi, router_segment false _ _ hn, CountedStream.setup_ready]

/-- A fixed finite router traverses arbitrarily many counted blocks router_after one
initialization, handles the short final block, and restores its local descriptor.
The finite table receives no widths or numerical block counts. -/
private theorem router_counted_blocks_frame (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8 * x.length + ((x.length - 1) / (IntMul.val y + 1)) * (4 * y.length + 3) +
        8 * y.length + 11 ∧
      machine.step^[t] (machine.initCfg x y) = frame x y x.length none := by
  let q := (x.length - 1) / router_blockSize y
  let j := q * router_blockSize y
  let r := x.length - j
  have hB : 0 < router_blockSize y := by dsimp only [router_blockSize]; omega
  have hjle : j ≤ x.length := by
    have hm := Nat.div_mul_le_self (x.length - 1) (router_blockSize y)
    dsimp only [j,q]
    omega
  have hjr : j + r = x.length := by dsimp only [r]; omega
  have hr : r ≤ router_blockSize y := by
    have hm := Nat.mod_lt (x.length - 1) hB
    have he := Nat.div_add_mod (x.length - 1) (router_blockSize y)
    rw [Nat.mul_comm] at he
    dsimp only [j,q,r]
    by_cases hn : x.length = 0
    · simp [hn]
    · omega
  obtain ⟨v,hv,hend⟩ := router_last_block x y j r hr hjr
  have hprefix : ∃ u : ℕ, u ≤ q * router_blockCost y ∧
      machine.step^[u] (router_lift false (CountedStream.readyFrame x y 0 .emit)) =
        router_lift false (CountedStream.readyFrame x y j .emit) := by
    by_cases hn : x.length = 0
    · refine ⟨0, by omega, ?_⟩
      have hj : j = 0 := by omega
      simp [hj]
    · have hjlt : j < x.length := by
        have hm := Nat.div_mul_le_self (x.length - 1) (router_blockSize y)
        dsimp only [j,q]
        omega
      simpa only [Nat.zero_add, j] using router_full_blocks x y q 0 (by simpa using hjlt)
  obtain ⟨u,hu,hstart⟩ := hprefix
  let initTime := 2 * x.length + 2 * y.length + 5
  refine ⟨v + u + initTime, ?_, ?_⟩
  · dsimp only [initTime,router_blockCost,router_blockSize] at *
    have hju : j = q * (IntMul.val y + 1) := rfl
    have hq : q = (x.length - 1) / (IntMul.val y + 1) := rfl
    have hcost : q * (6 * (IntMul.val y + 1) + 4 * y.length + 3) =
        6 * j + q * (4 * y.length + 3) := by rw [hju]; ring
    rw [hcost] at hu
    rw [← hq]
    omega
  · rw [Function.iterate_add_apply, router_setup, Function.iterate_add_apply, hstart, hend]

/-- Full output correctness together with the reusable restored tape interface. -/
theorem counted_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8 * x.length + ((x.length - 1) / (IntMul.val y + 1)) * (4 * y.length + 3) +
        8 * y.length + 11 ∧
      machine.HaltsWithOutput x y t x ∧
      machine.step^[t] (machine.initCfg x y) = frame x y x.length none := by
  obtain ⟨t,ht,he⟩ := router_counted_blocks_frame x y
  refine ⟨t,ht,?_,he⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [he]
  constructor
  · rfl
  · change machine.tapeOf ((x.take x.length).map machine.bitSym) = machine.tapeOf (x.map machine.bitSym)
    simp

end IntMul.CountedRouter


open IntMul.CountedRouter

theorem solution (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8 * x.length + ((x.length - 1) / (IntMul.val y + 1)) * (4 * y.length + 3) +
        8 * y.length + 11 ∧
      machine.HaltsWithOutput x y t x ∧
      machine.step^[t] (machine.initCfg x y) = frame x y x.length none :=
  IntMul.CountedRouter.counted_blocks x y

#print axioms solution
