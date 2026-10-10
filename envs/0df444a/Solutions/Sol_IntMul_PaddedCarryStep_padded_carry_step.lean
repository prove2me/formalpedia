-- Prove2me | solution 1 for IntMul.PaddedCarryStep.padded_carry_step
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T10:38:46.883976+00:00
-- url     : https://prove2.me/submissions/9bf9078d-d20b-4a5d-bb35-4e7c751b9eb6

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Definitions.Def_IntMul_PaddedCarryStep
import Theorems.Thm_IntMul_CarryStep_carry_step
import Theorems.Thm_IntMul_FiniteCaller_simulate_run


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



namespace IntMul.CountedStream

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulpaddedcarryzerocounter_zero_cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

/-- A proof-only constant-zero input. The physical zero-generator discards
this virtual bank and compiles the literal symbol zero into its finite table.
Output and both counter banks are genuine marked physical tapes. -/
private def zeroFrame (z bits : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i=0 then fun _ => Sym.zero
    else if i=1 then machine.tapeOf (List.replicate j Sym.zero)
    else if i=2 then machine.tapeOf (Sym.sep::(bits.reverse.map machine.bitSym++[Sym.sep]))
    else machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep]))
  head := fun i => if i=0 ∨ i=1 then j+1 else if i=2 then bits.length+1 else z.length+1

private theorem owned_intmulpaddedcarryzerocounter_counter_zero_frame (z old bits : List Bool) (j : ℕ) (q₀ q : State) :
    counterFrame (zeroFrame z old j q₀) q bits=zeroFrame z bits j q := by
  apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [counterFrame,zeroFrame]
  · funext i
    fin_cases i <;> simp [counterFrame,zeroFrame]

private theorem zero_counter (z bits : List Bool) (j : ℕ) :
    machine.step^[counterSteps bits] (zeroFrame z bits j .carry)=
      zeroFrame z (updated bits) j (.done (underflow bits)) := by
  rw [←owned_intmulpaddedcarryzerocounter_counter_zero_frame z bits bits j .carry .carry,counter_correct,owned_intmulpaddedcarryzerocounter_counter_zero_frame]

private theorem owned_intmulpaddedcarryzerocounter_zero_append (j : ℕ) :
    Function.update (machine.tapeOf (List.replicate j Sym.zero)) (j+1) Sym.zero=
      machine.tapeOf (List.replicate (j+1) Sym.zero) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p=j
    · subst p
      simp [MultitapeTM.tapeOf,List.getD_replicate]
    · rw [Function.update_of_ne (by omega : p+1≠j+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hl : p < j
      · rw [List.getD_replicate _ hl,List.getD_replicate _ (by omega)]
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

private theorem zero_emit (z bits : List Bool) (j : ℕ) :
    machine.step (zeroFrame z bits j .emit)=zeroFrame z bits (j+1) .carry := by
  let a : Fin 4 → Sym := fun i => (zeroFrame z bits j .emit).cells i ((zeroFrame z bits j .emit).head i)
  have hi : a 0=Sym.zero := rfl
  have ho : a 1=Sym.blank := by
    change (List.replicate j Sym.zero).getD j Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ (by simp)
  have ht : transition .emit a=(.carry,fun i => (if i=1 then Sym.zero else a i,
      if i=0 ∨ i=1 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,hi]
    simp only [true_or,ite_true]
    congr 1
    funext i
    fin_cases i
    · simp [hi,safeStep]
    · simp [ho,safeStep]
    · exact safe_stay _
    · exact safe_stay _
  change transition (zeroFrame z bits j .emit).state
    (fun i => (zeroFrame z bits j .emit).cells i ((zeroFrame z bits j .emit).head i))=_ at ht
  apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact owned_intmulpaddedcarryzerocounter_zero_append j
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [zeroFrame] <;> omega

private theorem zero_done_false (z bits : List Bool) (j : ℕ) :
    machine.step (zeroFrame z bits j (.done false))=zeroFrame z bits j .emit := by
  have ht : transition (.done false) (fun i => (zeroFrame z bits j (.done false)).cells i
      ((zeroFrame z bits j (.done false)).head i))=
      (.emit,fun i => ((zeroFrame z bits j (.done false)).cells i
        ((zeroFrame z bits j (.done false)).head i),Move.stay)) := by
    simp [transition,rawTransition,safe_stay]
  change transition (zeroFrame z bits j (.done false)).state
    (fun i => (zeroFrame z bits j (.done false)).cells i
      ((zeroFrame z bits j (.done false)).head i))=_ at ht
  apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem zero_done_true (z bits : List Bool) (j : ℕ) :
    machine.step (zeroFrame z bits j (.done true))=zeroFrame z bits j .resetLeft := by
  have ht : transition (.done true) (fun i => (zeroFrame z bits j (.done true)).cells i
      ((zeroFrame z bits j (.done true)).head i))=
      (.resetLeft,fun i => ((zeroFrame z bits j (.done true)).cells i
        ((zeroFrame z bits j (.done true)).head i),Move.stay)) := by
    simp [transition,rawTransition,safe_stay]
  change transition (zeroFrame z bits j (.done true)).state
    (fun i => (zeroFrame z bits j (.done true)).cells i
      ((zeroFrame z bits j (.done true)).head i))=_ at ht
  apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem zero_reset (z bits : List Bool) (j : ℕ) (hw : bits.length=z.length) :
    machine.step^[2*z.length+2] (zeroFrame z bits j .resetLeft)=
      zeroFrame z z.reverse j .halt := by
  have he : zeroFrame z bits j .resetLeft=
      resetFrame (zeroFrame z bits j .resetLeft) .resetLeft bits.reverse z (bits.reverse.length+1) := by
    apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
    · rfl
    · funext i
      fin_cases i <;> simp [zeroFrame,resetFrame]
    · funext i
      fin_cases i <;> simp [zeroFrame,resetFrame,hw]
  have hr := template_reset_correct (zeroFrame z bits j .resetLeft) bits.reverse z (by simpa using hw)
  simp only [List.length_reverse,hw] at hr
  rw [he]
  simp only [List.length_reverse,hw]
  rw [hr]
  apply owned_intmulpaddedcarryzerocounter_zero_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [zeroFrame,resetFrame]
  · funext i
    fin_cases i <;> simp [zeroFrame,resetFrame]

end IntMul.CountedStream



namespace IntMul.CountedStream

private theorem zero_cycle (z bits : List Bool) (j : ℕ) (hp : 0 < value bits) :
    machine.step^[counterSteps bits+2] (zeroFrame z bits j .carry)=
      zeroFrame z (updated bits) (j+1) .carry := by
  have h₁ : machine.step^[counterSteps bits+1] (zeroFrame z bits j .carry)=
      zeroFrame z (updated bits) j .emit := by
    rw [Function.iterate_succ_apply',zero_counter,(decrement_positive bits hp).1,zero_done_false]
  rw [show counterSteps bits+2=(counterSteps bits+1)+1 by omega,
    Function.iterate_succ_apply',h₁,zero_emit]

private theorem zero_terminal (z bits : List Bool) (j : ℕ)
    (hw : bits.length=z.length) (hz : value bits=0) :
    machine.step^[counterSteps bits+2*z.length+3] (zeroFrame z bits j .carry)=
      zeroFrame z z.reverse j .halt := by
  have h₁ : machine.step^[counterSteps bits+1] (zeroFrame z bits j .carry)=
      zeroFrame z (updated bits) j .resetLeft := by
    rw [Function.iterate_succ_apply',zero_counter,(underflow_iff_zero bits).mpr hz,zero_done_true]
  rw [show counterSteps bits+2*z.length+3=(2*z.length+2)+(counterSteps bits+1) by omega,
    Function.iterate_add_apply,h₁,zero_reset z (updated bits) j (by rw [updated_length,hw])]

private theorem zero_run (z bits : List Bool) (j n : ℕ)
    (hw : bits.length=z.length) (hv : value bits=n) :
    machine.step^[2*n+totalCounterSteps (n+1) bits+2*z.length+3]
      (zeroFrame z bits j .carry)=zeroFrame z z.reverse (j+n) .halt := by
  induction n generalizing bits j with
  | zero =>
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,totalCounterSteps] using zero_terminal z bits j hw hv
  | succ n ih =>
    have hp : 0 < value bits := by omega
    have hu : value (updated bits)=n := by have h := (decrement_positive bits hp).2;omega
    have ht : 2*(n+1)+totalCounterSteps ((n+1)+1) bits+2*z.length+3=
        (2*n+totalCounterSteps (n+1) (updated bits)+2*z.length+3)+(counterSteps bits+2) := by
      rw [totalCounterSteps]
      omega
    rw [ht,Function.iterate_add_apply,zero_cycle z bits j hp]
    have hr := ih (updated bits) (j+1) (by rw [updated_length,hw]) hu
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

/-- Exact zero count from the saved descriptor, including the final failed
decrement, every finite dispatch and a real full template reset. -/
private theorem descriptor_zero_run (z : List Bool) :
    ∃ t : ℕ, t ≤ 6*val z+4*z.length+7 ∧
      machine.step^[t] (zeroFrame z z.reverse 0 .carry)=
        zeroFrame z z.reverse (val z) .halt := by
  have hv : value z.reverse=val z := by
    change BinaryAdder.littleVal z.reverse=val z
    rw [←BinaryAdder.val_reverse_little,List.reverse_reverse]
  refine ⟨2*val z+totalCounterSteps (val z+1) z.reverse+2*z.length+3,?_,?_⟩
  · have hc := total_counter_steps_bound (val z+1) z.reverse
    rw [List.length_reverse] at hc
    omega
  · simpa only [Nat.zero_add] using zero_run z z.reverse 0 (val z) (by simp) hv

end IntMul.CountedStream



namespace IntMul.PaddedCarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem owned_intmulpaddedcarryprograms_safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private theorem owned_intmulpaddedcarryprograms_safe_main (q : CarryStep.machine.K) (a : Fin 9 → Sym) (j : Fin 9) :
    safeStep (a j) ((CarryStep.machine.δ q a).2 j).1 ((CarryStep.machine.δ q a).2 j).2=
      (CarryStep.machine.δ q a).2 j := by
  apply owned_intmulpaddedcarryprograms_safe_identity
  · exact CarryStep.machine.start_preserved q a j
  · exact CarryStep.machine.start_only_at_start q a j

private theorem owned_intmulpaddedcarryprograms_safe_zero (q : CountedStream.State) (a : Fin 4 → Sym) (j : Fin 4) :
    safeStep (a j) ((CountedStream.machine.δ q a).2 j).1 ((CountedStream.machine.δ q a).2 j).2=
      (CountedStream.machine.δ q a).2 j := by
  apply owned_intmulpaddedcarryprograms_safe_identity
  · exact CountedStream.machine.start_preserved q a j
  · exact CountedStream.machine.start_only_at_start q a j

private noncomputable def mainView (c : CarryStep.machine.Cfg) : subroutine.Cfg where
  state := mainState c.state
  cells := fun i => if h : i.val < 9 then c.cells ⟨i.val,h⟩ else subroutine.tapeOf []
  head := fun i => if h : i.val < 9 then c.head ⟨i.val,h⟩ else 0

private noncomputable def zeroView (x y z : List Bool) (c : CountedStream.machine.Cfg) : subroutine.Cfg where
  state := zeroState c.state
  cells := fun i => if i=6 then c.cells 2 else if i=7 then c.cells 3 else if i=9 then c.cells 1
    else if h : i.val < 9 then (CarryStep.finalFrame x y z).cells ⟨i.val,h⟩ else subroutine.tapeOf []
  head := fun i => if i=6 then c.head 2 else if i=7 then c.head 3 else if i=9 then c.head 1
    else if h : i.val < 9 then (CarryStep.finalFrame x y z).head ⟨i.val,h⟩ else 0

private theorem main_step (c : CarryStep.machine.Cfg) :
    subroutine.step (mainView c)=mainView (CarryStep.machine.step c) := by
  let a : Fin 10 → Sym := fun i => (mainView c).cells i ((mainView c).head i)
  let b : Fin 9 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (mainTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (mainState c.state) a=(mainState (CarryStep.machine.δ c.state b).1,
      mainAction a (CarryStep.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,CarryStep.machine.halt_fixed b]
      simp only [mainState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [mainState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 0
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 1
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 2
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 3
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 4
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 5
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 6
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 7
      · exact owned_intmulpaddedcarryprograms_safe_main c.state b 8
      · exact safe_stay _
  change transition (mainView c).state (fun i => (mainView c).cells i ((mainView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem main_run (c : CarryStep.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (mainView c)=mainView (CarryStep.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,main_step,Function.iterate_succ_apply']

private theorem zero_input_step (c : CountedStream.machine.Cfg) :
    (CountedStream.machine.step c).cells 0=c.cells 0 := by
  change Function.update (c.cells 0) (c.head 0)
    ((CountedStream.machine.δ c.state (fun i => c.cells i (c.head i))).2 0).1=c.cells 0
  have hi := CountedStream.machine.input_readonly c.state (fun i => c.cells i (c.head i))
  change ((CountedStream.machine.δ c.state (fun i => c.cells i (c.head i))).2 0).1=c.cells 0 (c.head 0) at hi
  rw [hi]
  exact Function.update_eq_self _ _

private theorem zero_input_run (c : CountedStream.machine.Cfg) (t : ℕ)
    (hz : c.cells 0=fun _ => Sym.zero) :
    (CountedStream.machine.step^[t] c).cells 0=fun _ => Sym.zero := by
  induction t with
  | zero => exact hz
  | succ t ih => rw [Function.iterate_succ_apply',zero_input_step,ih]

private theorem zero_step (x y z : List Bool) (c : CountedStream.machine.Cfg)
    (hz : c.cells 0=fun _ => Sym.zero) :
    subroutine.step (zeroView x y z c)=zeroView x y z (CountedStream.machine.step c) := by
  let a : Fin 10 → Sym := fun i => (zeroView x y z c).cells i ((zeroView x y z c).head i)
  let b : Fin 4 → Sym := fun j => c.cells j (c.head j)
  have ha : zeroSymbols a=b := by
    funext j
    fin_cases j
    · exact (congrFun hz (c.head 0)).symm
    · rfl
    · rfl
    · rfl
  have ht : transition (zeroState c.state) a=(zeroState (CountedStream.machine.δ c.state b).1,
      zeroAction a (CountedStream.machine.δ c.state b).2) := by
    by_cases h : c.state=.halt
    · rw [h,CountedStream.machine.halt_fixed b]
      simp only [zeroState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [zeroState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact owned_intmulpaddedcarryprograms_safe_zero c.state b 2
      · exact owned_intmulpaddedcarryprograms_safe_zero c.state b 3
      · exact safe_stay _
      · exact owned_intmulpaddedcarryprograms_safe_zero c.state b 1
  change transition (zeroView x y z c).state
    (fun i => (zeroView x y z c).cells i ((zeroView x y z c).head i))=_ at ht
  apply cfg_ext
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
    · rfl
    · rfl
    · exact Function.update_eq_self _ _
    · rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem zero_run (x y z : List Bool) (c : CountedStream.machine.Cfg) (t : ℕ)
    (hz : c.cells 0=fun _ => Sym.zero) :
    subroutine.step^[t] (zeroView x y z c)=zeroView x y z (CountedStream.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,zero_step x y z _ (zero_input_run c t hz),Function.iterate_succ_apply']

private theorem padded_initial (x y z : List Bool) :
    initialFrame x y z=FiniteCaller.embed subroutine Phase .main .main dispatch
      (mainView (CarryStep.initialFrame x y z)) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end IntMul.PaddedCarryStep



namespace IntMul.PaddedCarryStep

open TapeCopy (Sym)

private theorem owned_intmulpaddedcarryframes_val_zeros (n : ℕ) : val (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,val] using ih

private theorem padding_length (x y z : List Bool) (hB : CarryStep.blockSize z ≤ x.length+1) :
    (paddingWord x y z).length=x.length := by
  simp only [paddingWord,List.length_append,List.length_replicate,List.length_reverse,
    CarryStep.carryWord,List.length_drop,List.length_reverse,CarryStep.sumWord,bin,List.length_ofFn]
  unfold CarryStep.blockSize at hB ⊢
  omega

private theorem padding_value (x y z : List Bool)
    (hc : val (CarryStep.carryWord x y z).reverse=(val x+val y)/(2^CarryStep.blockSize z)) :
    val (paddingWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by
  rw [paddingWord,BinaryAdder.val_append,owned_intmulpaddedcarryframes_val_zeros,Nat.mul_zero,Nat.zero_add,hc]

private theorem padding_bin (x y z : List Bool) (hB : CarryStep.blockSize z ≤ x.length+1)
    (hc : val (CarryStep.carryWord x y z).reverse=(val x+val y)/(2^CarryStep.blockSize z)) :
    paddingWord x y z=nextCarryWord x y z := by
  have hr := BinaryAdder.bin_value_roundtrip (paddingWord x y z)
  rw [padding_length x y z hB,padding_value x y z hc] at hr
  exact hr.symm

private noncomputable def openPadFrame (x y z : List Bool) : subroutine.Cfg :=
  {zeroView x y z (CountedStream.zeroFrame z z.reverse 0 .carry) with
    state := copyState .openPad
    head := Function.update (zeroView x y z (CountedStream.zeroFrame z z.reverse 0 .carry)).head 9 0}

private noncomputable def reverseFrame (x y z : List Bool) (j : ℕ) (q : CopyState) : subroutine.Cfg where
  state := copyState q
  cells := fun i => if h : i.val < 9 then (CarryStep.finalFrame x y z).cells ⟨i.val,h⟩
    else subroutine.tapeOf (List.replicate (val z) Sym.zero++
      (((CarryStep.carryWord x y z).drop j).reverse.map subroutine.bitSym))
  head := fun i => if i=8 then j else if h : i.val < 9 then (CarryStep.finalFrame x y z).head ⟨i.val,h⟩
    else val z+((CarryStep.carryWord x y z).length-j)+1

private noncomputable def turnFrame (x y z : List Bool) : subroutine.Cfg :=
  {reverseFrame x y z (CarryStep.carryWord x y z).length .turnCarry with
    head := Function.update (reverseFrame x y z (CarryStep.carryWord x y z).length .turnCarry).head
      8 ((CarryStep.carryWord x y z).length+1)}

private noncomputable def reverseFinal (x y z : List Bool) : subroutine.Cfg :=
  {reverseFrame x y z 0 .reverseCarry with state := none}

private theorem main_to_pad (x y z : List Bool) :
    {mainView (CarryStep.finalFrame x y z) with state := copyState .openPad}=openPadFrame x y z := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [mainView,openPadFrame,zeroView,CountedStream.zeroFrame,CarryStep.finalFrame] <;> rfl
  · funext i
    fin_cases i <;> simp [mainView,openPadFrame,zeroView,CountedStream.zeroFrame,CarryStep.finalFrame]

private theorem pad_to_turn (x y z : List Bool) (hB : CarryStep.blockSize z ≤ x.length+1) :
    {zeroView x y z (CountedStream.zeroFrame z z.reverse (val z) .halt) with
      state := copyState .turnCarry}=turnFrame x y z := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [zeroView,CountedStream.zeroFrame,turnFrame,reverseFrame,CarryStep.finalFrame] <;> rfl
  · funext i
    fin_cases i <;> simp [zeroView,CountedStream.zeroFrame,turnFrame,reverseFrame,
      CarryStep.finalFrame,CarryStep.carryWord,CarryStep.sumWord,bin,CarryStep.blockSize] <;>
      simp [CarryStep.blockSize] at hB <;> omega

private theorem reverse_to_final (x y z : List Bool) (hB : CarryStep.blockSize z ≤ x.length+1)
    (hc : val (CarryStep.carryWord x y z).reverse=(val x+val y)/(2^CarryStep.blockSize z)) :
    FiniteCaller.returned subroutine Phase .main .reverse dispatch (reverseFinal x y z)=finalFrame x y z := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i
    all_goals try rfl
    change subroutine.tapeOf (List.replicate (val z) Sym.zero++
      (CarryStep.carryWord x y z).reverse.map subroutine.bitSym)=
        machine.tapeOf ((nextCarryWord x y z).map machine.bitSym)
    have hp := padding_bin x y z hB hc
    have hm : (paddingWord x y z).map subroutine.bitSym=
        List.replicate (val z) Sym.zero++(CarryStep.carryWord x y z).reverse.map subroutine.bitSym := by
      simp [paddingWord,MultitapeTM.bitSym]
    rw [←hm,hp]
    rfl
  · funext i
    fin_cases i
    all_goals try rfl
    have hl := padding_length x y z hB
    simp only [paddingWord,List.length_append,List.length_replicate,List.length_reverse] at hl
    change val z+(CarryStep.carryWord x y z).length-0+1=x.length+1
    omega

end IntMul.PaddedCarryStep



namespace IntMul.PaddedCarryStep

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulpaddedcarrycopy_safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases h : s=Sym.start <;> simp [safeStep,h]

private theorem owned_intmulpaddedcarrycopy_bits_read (w : List Bool) (j : ℕ) (hj : j < w.length) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)=subroutine.bitSym w[j] := by
  change (w.map subroutine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem owned_intmulpaddedcarrycopy_bits_blank (w : List Bool) :
    subroutine.tapeOf (w.map subroutine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map subroutine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem owned_intmulpaddedcarrycopy_append_one (w : List Sym) (a : Sym) :
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

private theorem open_pad_step (x y z : List Bool) :
    subroutine.step (openPadFrame x y z)=
      zeroView x y z (CountedStream.zeroFrame z z.reverse 0 .carry) := by
  let a : Fin 10 → Sym := fun i => (openPadFrame x y z).cells i ((openPadFrame x y z).head i)
  have ht : transition (copyState .openPad) a=(zeroState .carry,
      fun i => (a i,if i=9 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,copyState,copyRaw]
    congr 1
    funext i
    fin_cases i
    all_goals first | exact safe_stay _ | exact owned_intmulpaddedcarrycopy_safe_right _
  change transition (openPadFrame x y z).state
    (fun i => (openPadFrame x y z).cells i ((openPadFrame x y z).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [openPadFrame,zeroView,CountedStream.zeroFrame]

private theorem turn_carry_step (x y z : List Bool) :
    subroutine.step (turnFrame x y z)=
      reverseFrame x y z (CarryStep.carryWord x y z).length .reverseCarry := by
  let a : Fin 10 → Sym := fun i => (turnFrame x y z).cells i ((turnFrame x y z).head i)
  have hi : a 8=Sym.blank := owned_intmulpaddedcarrycopy_bits_blank (CarryStep.carryWord x y z)
  have ht : transition (copyState .turnCarry) a=(copyState .reverseCarry,
      fun i => (a i,if i=8 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,copyState,copyRaw]
    congr 1
    funext i
    fin_cases i
    all_goals first | exact safe_stay _ | simp [hi,safeStep]
  change transition (turnFrame x y z).state
    (fun i => (turnFrame x y z).cells i ((turnFrame x y z).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [turnFrame,reverseFrame]

private theorem owned_intmulpaddedcarrycopy_reverse_transition (a : Fin 10 → Sym) (b : Bool)
    (hi : a 8=subroutine.bitSym b) (ho : a 9=Sym.blank) :
    transition (copyState .reverseCarry) a=(copyState .reverseCarry,
      fun i => (if i=9 then a 8 else a i,if i=8 then Move.left else if i=9 then Move.right else Move.stay)) := by
  have hb : a 8=Sym.zero ∨ a 8=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,copyState,copyRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  all_goals first | exact safe_stay _ | (cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym])

private theorem reverse_step (x y z : List Bool) (j : ℕ) (hj : j+1 ≤ (CarryStep.carryWord x y z).length) :
    subroutine.step (reverseFrame x y z (j+1) .reverseCarry)=reverseFrame x y z j .reverseCarry := by
  let b := (CarryStep.carryWord x y z)[j]'(by omega)
  have hi : (reverseFrame x y z (j+1) .reverseCarry).cells 8
      ((reverseFrame x y z (j+1) .reverseCarry).head 8)=subroutine.bitSym b := owned_intmulpaddedcarrycopy_bits_read _ j (by omega)
  let w := List.replicate (val z) Sym.zero++
    (((CarryStep.carryWord x y z).drop (j+1)).reverse.map subroutine.bitSym)
  have hl : w.length=val z+((CarryStep.carryWord x y z).length-(j+1)) := by simp [w]
  have ho : (reverseFrame x y z (j+1) .reverseCarry).cells 9
      ((reverseFrame x y z (j+1) .reverseCarry).head 9)=Sym.blank := by
    change w.getD (val z+((CarryStep.carryWord x y z).length-(j+1))) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulpaddedcarrycopy_reverse_transition (fun i => (reverseFrame x y z (j+1) .reverseCarry).cells i
    ((reverseFrame x y z (j+1) .reverseCarry).head i)) b hi ho
  change transition (reverseFrame x y z (j+1) .reverseCarry).state
    (fun i => (reverseFrame x y z (j+1) .reverseCarry).cells i
      ((reverseFrame x y z (j+1) .reverseCarry).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    all_goals try exact Function.update_eq_self _ _
    change Function.update (subroutine.tapeOf w)
      (val z+((CarryStep.carryWord x y z).length-(j+1))+1)
      ((reverseFrame x y z (j+1) .reverseCarry).cells 8
        ((reverseFrame x y z (j+1) .reverseCarry).head 8))=
      subroutine.tapeOf (List.replicate (val z) Sym.zero++
        (((CarryStep.carryWord x y z).drop j).reverse.map subroutine.bitSym))
    rw [hi]
    have hd : (CarryStep.carryWord x y z).drop j=b::(CarryStep.carryWord x y z).drop (j+1) :=
      List.drop_eq_getElem_cons (by omega)
    rw [hd,List.reverse_cons,List.map_append,List.map_singleton]
    have hw := owned_intmulpaddedcarrycopy_append_one w (subroutine.bitSym b)
    rw [hl] at hw
    simpa only [w,List.append_assoc] using hw
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [reverseFrame] <;> omega

private theorem reverse_run (x y z : List Bool) (j : ℕ) (hj : j ≤ (CarryStep.carryWord x y z).length) :
    subroutine.step^[j] (reverseFrame x y z j .reverseCarry)=reverseFrame x y z 0 .reverseCarry := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,reverse_step x y z j hj,ih (by omega)]

private theorem reverse_halt_step (x y z : List Bool) :
    subroutine.step (reverseFrame x y z 0 .reverseCarry)=reverseFinal x y z := by
  let a : Fin 10 → Sym := fun i => (reverseFrame x y z 0 .reverseCarry).cells i
    ((reverseFrame x y z 0 .reverseCarry).head i)
  have hi : a 8=Sym.start := rfl
  have ht : transition (copyState .reverseCarry) a=(none,fun i => (a i,Move.stay)) := by
    simp only [transition,rawTransition,copyState,copyRaw,hi]
    rw [if_neg (by decide : ¬(Sym.start=Sym.zero ∨ Sym.start=Sym.one))]
    simp only [safe_stay]
  change transition (reverseFrame x y z 0 .reverseCarry).state
    (fun i => (reverseFrame x y z 0 .reverseCarry).cells i
      ((reverseFrame x y z 0 .reverseCarry).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem reverse_complete (x y z : List Bool) :
    subroutine.step^[(CarryStep.carryWord x y z).length+2] (turnFrame x y z)=reverseFinal x y z := by
  have hs : subroutine.step^[(CarryStep.carryWord x y z).length+1] (turnFrame x y z)=
      reverseFrame x y z 0 .reverseCarry := by
    rw [Function.iterate_succ_apply,turn_carry_step,reverse_run x y z _ le_rfl]
  rw [show (CarryStep.carryWord x y z).length+2=((CarryStep.carryWord x y z).length+1)+1 by omega,
    Function.iterate_succ_apply',hs,reverse_halt_step]

end IntMul.PaddedCarryStep



namespace IntMul.PaddedCarryStep

private theorem owned_intmulpaddedcarryprimary_zeros_complete (x y z : List Bool) :
    ∃ t : ℕ, t ≤ 6*CarryStep.blockSize z+4*z.length+2 ∧
      subroutine.step^[t] (openPadFrame x y z)=
        zeroView x y z (CountedStream.zeroFrame z z.reverse (val z) .halt) := by
  obtain ⟨t,ht,he⟩ := CountedStream.descriptor_zero_run z
  refine ⟨t+1,?_,?_⟩
  · unfold CarryStep.blockSize
    omega
  · rw [Function.iterate_succ_apply,open_pad_step,zero_run x y z _ t (by rfl),he]

private theorem owned_intmulpaddedcarryprimary_after_main (x y z : List Bool) :
    FiniteCaller.returned subroutine Phase .main .main dispatch (mainView (CarryStep.finalFrame x y z))=
    FiniteCaller.embed subroutine Phase .main .zeros dispatch (openPadFrame x y z) := by
  have h := main_to_pad x y z
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem owned_intmulpaddedcarryprimary_after_zeros (x y z : List Bool) (hB : CarryStep.blockSize z ≤ x.length+1) :
    FiniteCaller.returned subroutine Phase .main .zeros dispatch
      (zeroView x y z (CountedStream.zeroFrame z z.reverse (val z) .halt))=
    FiniteCaller.embed subroutine Phase .main .reverse dispatch (turnFrame x y z) := by
  have h := pad_to_turn x y z hB
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply cfg_ext
  · rfl
  · exact hc
  · exact hh

/-- One complete physical carry update retaining its low digit and emitting
an exact n-bit outgoing carry operand ready for another arithmetic update.
Every zero, counter transition, reverse-copy step and caller return is paid. -/
private theorem padded_carry_step (x y z : List Bool) (h : x.length=y.length)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 10*x.length+10*CarryStep.blockSize z+12*z.length+36 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by
  obtain ⟨u,hu,he,hhalt,hd,hc⟩ := CarryStep.carry_step x y z h hB
  have hmain : subroutine.step^[u] (mainView (CarryStep.initialFrame x y z))=
      mainView (CarryStep.finalFrame x y z) := by rw [main_run,he]
  obtain ⟨a,ha,hea⟩ := (FiniteCaller.simulate_run subroutine Phase .main .main dispatch
    (mainView (CarryStep.initialFrame x y z)) u).2 (by rw [hmain];rfl)
  rw [hmain,owned_intmulpaddedcarryprimary_after_main] at hea
  obtain ⟨v,hv,hzero⟩ := owned_intmulpaddedcarryprimary_zeros_complete x y z
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .main .zeros dispatch
    (openPadFrame x y z) v).2 (by rw [hzero];rfl)
  rw [hzero,owned_intmulpaddedcarryprimary_after_zeros x y z hB] at heb
  obtain ⟨c,hcc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .main .reverse dispatch
    (turnFrame x y z) ((CarryStep.carryWord x y z).length+2)).2 (by rw [reverse_complete];rfl)
  rw [reverse_complete,reverse_to_final x y z hB hc] at hec
  have hfinal : machine.step^[c+(b+a)] (initialFrame x y z)=finalFrame x y z := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,padded_initial,hea,heb,hec]
  refine ⟨c+(b+a),?_,hfinal,?_,hd,?_⟩
  · have hl : (CarryStep.carryWord x y z).length=x.length+1-CarryStep.blockSize z := by
      simp [CarryStep.carryWord,CarryStep.sumWord,bin]
    rw [hl] at hcc
    omega
  · rw [hfinal];rfl
  · rw [←padding_bin x y z hB hc]
    exact padding_value x y z hc

end IntMul.PaddedCarryStep



open IntMul IntMul.PaddedCarryStep

theorem solution (x y z : List Bool) (h : x.length=y.length)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 10*x.length+10*CarryStep.blockSize z+12*z.length+36 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) :=
  IntMul.PaddedCarryStep.padded_carry_step x y z h hB

#print axioms solution
