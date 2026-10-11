-- Prove2me | solution 1 for IntMul.GrowingCounter.counter_width_logarithmic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T15:05:35.87108+00:00
-- url     : https://prove2.me/submissions/45df1bac-0986-4596-9dd9-89abf8c1ba05

import Definitions.Def_IntMul_GrowingCounter
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.GrowingCounter

private inductive Canonical : List Bool → Prop
  | nil : Canonical []
  | one : Canonical [true]
  | cons (b : Bool) {bs : List Bool} : Canonical bs → bs≠[] → Canonical (b::bs)

private theorem increment_nonempty (bs : List Bool) : increment bs≠[] := by
  cases bs with
  | nil => simp [increment]
  | cons b bs => cases b <;> simp [increment]

private theorem canonical_tail (b : Bool) (bs : List Bool) (h : Canonical (b::bs)) : Canonical bs := by
  cases h with
  | one => exact .nil
  | cons b h hn => exact h

private theorem increment_canonical (bs : List Bool) (h : Canonical bs) : Canonical (increment bs) := by
  induction bs with
  | nil => exact .one
  | cons b bs ih =>
      have hb := canonical_tail b bs h
      cases b with
      | false =>
          cases bs with
          | nil => exact .one
          | cons c cs => exact .cons true hb (List.cons_ne_nil _ _)
      | true => exact .cons false (ih hb) (increment_nonempty bs)

private theorem iterate_canonical (n : ℕ) (bs : List Bool) (h : Canonical bs) : Canonical (iterateCounter n bs) := by
  induction n generalizing bs with
  | zero => exact h
  | succ n ih => exact ih (increment bs) (increment_canonical bs h)

private theorem increment_value (bits : List Bool) : BinaryAdder.littleVal (increment bits)=BinaryAdder.littleVal bits+1 := by
  induction bits with
  | nil => simp [increment,BinaryAdder.littleVal]
  | cons b bs ih =>
      cases b <;> simp only [increment,BinaryAdder.littleVal,ih,Bool.toNat_false,Bool.toNat_true] <;> omega

private theorem iterate_value (n : ℕ) (bits : List Bool) : BinaryAdder.littleVal (iterateCounter n bits)=BinaryAdder.littleVal bits+n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih => rw [iterateCounter,ih,increment_value];omega

private theorem value_upper (bs : List Bool) : BinaryAdder.littleVal bs<2^bs.length := by
  induction bs with
  | nil => simp [BinaryAdder.littleVal]
  | cons b bs ih =>
      cases b <;> simp only [BinaryAdder.littleVal,List.length_cons,pow_succ,
        Bool.toNat_false,Bool.toNat_true] <;> omega

private theorem value_lower (bs : List Bool) (h : Canonical bs) (hn : bs≠[]) :
    2^(bs.length-1)≤BinaryAdder.littleVal bs := by
  induction h with
  | nil => exact False.elim (hn rfl)
  | one => simp [BinaryAdder.littleVal]
  | @cons b bs h hne ih =>
      have hp : 0<bs.length := List.length_pos_iff_ne_nil.mpr hne
      have hi := ih hne
      have he : 2^bs.length=2*2^(bs.length-1) := by
        calc
          2^bs.length=2^((bs.length-1)+1) := congrArg (2^·) (by omega)
          _=2^(bs.length-1)*2 := pow_succ _ _
          _=2*2^(bs.length-1) := Nat.mul_comm _ _
      simp only [List.length_cons,Nat.add_sub_cancel,BinaryAdder.littleVal]
      rw [he]
      omega

/-- The physically growing counter has exactly the least width needed to
represent its value, including the empty representation of zero. -/
private theorem counter_width_logarithmic (n : ℕ) :
    (iterateCounter n []).length=Nat.clog 2 (n+1) ∧
      BinaryAdder.littleVal (iterateCounter n [])=n ∧
      (iterateCounter n []=[] ↔ n=0) := by
  let bs := iterateCounter n []
  have hc : Canonical bs := iterate_canonical n [] .nil
  have hv : BinaryAdder.littleVal bs=n := by simpa [bs,BinaryAdder.littleVal] using iterate_value n []
  have hu : n+1≤2^bs.length := by have h := value_upper bs;rw [hv] at h;omega
  have hlo : Nat.clog 2 (n+1)≤bs.length := Nat.clog_le_of_le_pow hu
  have heq : bs.length=Nat.clog 2 (n+1) := by
    by_cases hn : bs=[]
    · have hz : n=0 := by rw [hn] at hv;simp [BinaryAdder.littleVal] at hv;omega
      simp [hn,hz]
    · have hl := value_lower bs hc hn
      rw [hv] at hl
      have hlt : bs.length-1<Nat.clog 2 (n+1) :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 (by omega)
      have hp : 0<bs.length := List.length_pos_iff_ne_nil.mpr hn
      omega
  refine ⟨heq,hv,?_⟩
  constructor
  · intro h;change bs=[] at h;rw [h] at hv;simp [BinaryAdder.littleVal] at hv;omega
  · intro h;change iterateCounter n []=[];rw [h];rfl

end IntMul.GrowingCounter

open IntMul IntMul.GrowingCounter

theorem solution (n : ℕ) :
    (iterateCounter n []).length=Nat.clog 2 (n+1) ∧
      BinaryAdder.littleVal (iterateCounter n [])=n ∧
      (iterateCounter n []=[] ↔ n=0) :=
  IntMul.GrowingCounter.counter_width_logarithmic n

#print axioms solution
