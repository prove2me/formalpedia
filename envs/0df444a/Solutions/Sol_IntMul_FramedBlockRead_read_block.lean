-- Prove2me | solution 1 for IntMul.FramedBlockRead.read_block
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T10:41:50.346009+00:00
-- url     : https://prove2.me/submissions/f3c63e37-2bbf-4644-a568-95d440fed373

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Definitions.Def_IntMul_FramedBlockRead


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



namespace IntMul.FramedBlockRead
open CountedStream
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulframedblockreadtrace_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulframedblockreadtrace_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulframedblockreadtrace_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
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

private theorem owned_intmulframedblockreadtrace_counter_frame_from_stream (pre x tail a y old bits : List Bool) (j : ℕ) (q₀ q : State)
    (h : bits.length = y.length) :
    counterFrame (frame pre x tail a y old j q₀) q bits = frame pre x tail a y bits j q := by
  apply owned_intmulframedblockreadtrace_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [CountedStream.counterFrame, frame]
  · funext i
    fin_cases i <;> simp [counterFrame, frame, h]

private theorem owned_intmulframedblockreadtrace_stream_counter (pre x tail a y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step^[counterSteps bits] (frame pre x tail a y bits j .carry) =
      frame pre x tail a y (updated bits) j (.done (underflow bits)) := by
  have hf := owned_intmulframedblockreadtrace_counter_frame_from_stream pre x tail a y bits bits j .carry .carry h
  rw [← hf, counter_correct]
  exact owned_intmulframedblockreadtrace_counter_frame_from_stream pre x tail a y bits (updated bits) j .carry (.done (underflow bits))
    (by rw [updated_length]; exact h)

private theorem owned_intmulframedblockreadtrace_emit_transition (a : Fin 4 → Sym) (b : Bool)
    (hb : a 0 = machine.bitSym b) (ho : a 1 = .blank) :
    transition .emit a = (.carry, fun i =>
      (if i = 1 then machine.bitSym b else a i, if i = 0 ∨ i = 1 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulframedblockreadtrace_safe_right _
  · change safeStep (a 1) (a 0) .right = (machine.bitSym b, .right)
    rw [ho, hb]
    cases b <;> decide
  · exact safe_stay _
  · exact safe_stay _

private theorem owned_intmulframedblockreadtrace_emit_step (pre x tail a y bits : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (frame pre x tail a y bits j .emit) = frame pre x tail a y bits (j + 1) .carry := by
  have hl : ((a++x.take j).map machine.bitSym).length = a.length+j := by
    simp [Nat.min_eq_left hj.le]
  have hr : (frame pre x tail a y bits j .emit).cells 0 ((frame pre x tail a y bits j .emit).head 0) = machine.bitSym x[j] := by
    change ((pre++x++tail).map machine.bitSym++Sym.sep::y.map machine.bitSym).getD
      (pre.length+j) machine.blank = _
    rw [List.map_append, List.map_append, List.append_assoc, List.append_assoc,
      List.getD_append_right _ _ _ _ (by simp), List.length_map]
    rw [show pre.length+j-pre.length=j by omega,
      List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have ho : (frame pre x tail a y bits j .emit).cells 1 ((frame pre x tail a y bits j .emit).head 1) = Sym.blank := by
    change ((a++x.take j).map machine.bitSym).getD (a.length+j) machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulframedblockreadtrace_emit_transition
    (fun i => (frame pre x tail a y bits j .emit).cells i ((frame pre x tail a y bits j .emit).head i)) x[j] hr ho
  change transition (frame pre x tail a y bits j .emit).state
    (fun i => (frame pre x tail a y bits j .emit).cells i ((frame pre x tail a y bits j .emit).head i)) = _ at ht
  apply owned_intmulframedblockreadtrace_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((frame pre x tail a y bits j .emit).cells 0) ((frame pre x tail a y bits j .emit).head 0)
        ((frame pre x tail a y bits j .emit).cells 0 ((frame pre x tail a y bits j .emit).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf ((a++x.take j).map machine.bitSym)) (a.length+j+1)
        (machine.bitSym x[j]) = machine.tapeOf ((a++x.take (j+1)).map machine.bitSym)
      have hnew : (a++x.take (j+1)).map machine.bitSym =
          (a++x.take j).map machine.bitSym++[machine.bitSym x[j]] := by
        rw [List.take_succ_eq_append_getElem hj, ←List.append_assoc,
          List.map_append]
        rfl
      rw [hnew]
      have hw := owned_intmulframedblockreadtrace_tapeOf_append_one machine ((a++x.take j).map machine.bitSym) (machine.bitSym x[j])
      rw [hl] at hw
      exact hw
    all_goals
      change Function.update ((frame pre x tail a y bits j .emit).cells _) ((frame pre x tail a y bits j .emit).head _)
        ((frame pre x tail a y bits j .emit).cells _ ((frame pre x tail a y bits j .emit).head _)) = _
      rw [Function.update_eq_self]
      rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [frame, Nat.add_assoc]

private theorem owned_intmulframedblockreadtrace_done_transition (a : Fin 4 → Sym) (f : Bool) :
    transition (.done f) a = (if f then .resetLeft else .emit, fun i => (a i, .stay)) := by
  simp [transition, rawTransition, safe_stay]

private theorem owned_intmulframedblockreadtrace_done_false_step (pre x tail a y bits : List Bool) (j : ℕ) :
    machine.step (frame pre x tail a y bits j (.done false)) = frame pre x tail a y bits j .emit := by
  have ht := owned_intmulframedblockreadtrace_done_transition (fun i => (frame pre x tail a y bits j (.done false)).cells i
    ((frame pre x tail a y bits j (.done false)).head i)) false
  change transition (frame pre x tail a y bits j (.done false)).state
    (fun i => (frame pre x tail a y bits j (.done false)).cells i
      ((frame pre x tail a y bits j (.done false)).head i)) = _ at ht
  apply owned_intmulframedblockreadtrace_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((frame pre x tail a y bits j (.done false)).cells i)
      ((frame pre x tail a y bits j (.done false)).head i)
      ((frame pre x tail a y bits j (.done false)).cells i ((frame pre x tail a y bits j (.done false)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulframedblockreadtrace_done_true_step (pre x tail a y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step (frame pre x tail a y bits j (.done true)) =
      resetFrame (frame pre x tail a y bits j (.done true)) .resetLeft bits.reverse y (y.length + 1) := by
  have ht := owned_intmulframedblockreadtrace_done_transition (fun i => (frame pre x tail a y bits j (.done true)).cells i
    ((frame pre x tail a y bits j (.done true)).head i)) true
  change transition (frame pre x tail a y bits j (.done true)).state
    (fun i => (frame pre x tail a y bits j (.done true)).cells i
      ((frame pre x tail a y bits j (.done true)).head i)) = _ at ht
  apply owned_intmulframedblockreadtrace_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((frame pre x tail a y bits j (.done true)).cells i)
      ((frame pre x tail a y bits j (.done true)).head i)
      ((frame pre x tail a y bits j (.done true)).cells i ((frame pre x tail a y bits j (.done true)).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [frame, resetFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [frame, resetFrame]


private theorem owned_intmulframedblockreadtrace_nonterminal_cycle (pre x tail a y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hp : 0 < value bits) :
    machine.step^[counterSteps bits + 2] (frame pre x tail a y bits j .emit) =
      frame pre x tail a y (updated bits) (j + 1) .emit := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulframedblockreadtrace_emit_step pre x tail a y bits j hj,
    Function.iterate_succ_apply', owned_intmulframedblockreadtrace_stream_counter pre x tail a y bits (j + 1) hw,
    (decrement_positive bits hp).1, owned_intmulframedblockreadtrace_done_false_step]

private theorem owned_intmulframedblockreadtrace_loop_run (pre x tail a y : List Bool) (n : ℕ) (bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hv : n ≤ value bits) (hx : j + n ≤ x.length) :
    machine.step^[2 * n + totalCounterSteps n bits] (frame pre x tail a y bits j .emit) =
      frame pre x tail a y (iterateCounter n bits) (j + n) .emit := by
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
        owned_intmulframedblockreadtrace_nonterminal_cycle pre x tail a y bits j (by omega) hw hp]
      have hr := ih (updated bits) (j + 1) (by rw [updated_length]; exact hw) (by omega) (by omega)
      simpa only [iterateCounter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private theorem owned_intmulframedblockreadtrace_terminal_cycle (pre x tail a y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hz : value bits = 0) :
    machine.step^[counterSteps bits + 2] (frame pre x tail a y bits j .emit) =
      resetFrame (frame pre x tail a y (updated bits) (j + 1) (.done true))
        .resetLeft (updated bits).reverse y (y.length + 1) := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulframedblockreadtrace_emit_step pre x tail a y bits j hj,
    Function.iterate_succ_apply', owned_intmulframedblockreadtrace_stream_counter pre x tail a y bits (j + 1) hw,
    (underflow_iff_zero bits).mpr hz]
  exact owned_intmulframedblockreadtrace_done_true_step pre x tail a y (updated bits) (j + 1) (by rw [updated_length]; exact hw)

/-- The last (B-th) emission detects underflow, then takes its actual dispatch
transition into reset. All previous emissions remain in the same finite loop. -/
private theorem owned_intmulframedblockreadtrace_block_run (pre x tail a y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits]
      (frame pre x tail a y bits j .emit) =
        resetFrame (frame pre x tail a y last (j + (value bits + 1)) (.done true))
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
  rw [ht, Function.iterate_add_apply, owned_intmulframedblockreadtrace_loop_run pre x tail a y (value bits) bits j hw le_rfl (by omega),
    owned_intmulframedblockreadtrace_terminal_cycle pre x tail a y (iterateCounter (value bits) bits) (j + value bits) (by omega) hn hz]
  simp only [Nat.add_assoc]

/-- Complete live block, including every payload, counter, dispatch, and reset
transition. The final full configuration also records both returned work heads. -/
private theorem owned_intmulframedblockreadtrace_block_reset_run (pre x tail a y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2)]
      (frame pre x tail a y bits j .emit) =
        resetFrame (frame pre x tail a y last (j + (value bits + 1)) (.done true))
          .halt y y (y.length + 1) := by
  dsimp only
  have hl : (updated (iterateCounter (value bits) bits)).reverse.length = y.length := by
    rw [List.length_reverse, updated_length, iterate_counter_length]
    exact hw
  rw [show 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2) =
      (2 * y.length + 2) + (2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits) by omega,
    Function.iterate_add_apply, owned_intmulframedblockreadtrace_block_run pre x tail a y bits j hw hx]
  have hr := template_reset_correct
    (frame pre x tail a y (updated (iterateCounter (value bits) bits)) (j + (value bits + 1)) (.done true))
      (updated (iterateCounter (value bits) bits)).reverse y hl
  rw [hl] at hr
  exact hr


private theorem owned_intmulframedblockreadtrace_ready_matches_stream (pre x tail a y : List Bool) (j : ℕ) (q : State) :
    ready pre x tail a y j q = frame pre x tail a y y.reverse j q := by
  apply owned_intmulframedblockreadtrace_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ready, frame]
  · funext i
    fin_cases i <;> simp [ready, frame]

private theorem owned_intmulframedblockreadtrace_reset_matches_ready (pre x tail a y old : List Bool) (j : ℕ) :
    resetFrame (frame pre x tail a y old j (.done true)) .halt y y (y.length + 1) =
      ready pre x tail a y j .halt := by
  apply owned_intmulframedblockreadtrace_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ready, frame, resetFrame]
  · funext i
    fin_cases i <;> simp [ready, frame, resetFrame]

private theorem read_block (pre x tail a y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (ready pre x tail a y 0 .emit) =
        ready pre x tail a y (IntMul.val y+1) .halt := by
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
  · rw [owned_intmulframedblockreadtrace_ready_matches_stream]
    have hr := owned_intmulframedblockreadtrace_block_reset_run pre x tail a y y.reverse 0 (by simp) (by simpa [hv] using hx)
    simpa only [clock, hv, owned_intmulframedblockreadtrace_reset_matches_ready, Nat.zero_add] using hr


end IntMul.FramedBlockRead



open IntMul IntMul.FramedBlockRead

theorem solution (pre x tail a y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (ready pre x tail a y 0 .emit) =
        ready pre x tail a y (IntMul.val y+1) .halt :=
  IntMul.FramedBlockRead.read_block pre x tail a y hx

#print axioms solution
