-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.selected_digit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:10:50.40668+00:00
-- url     : https://prove2.me/submissions/5857ab65-f327-4513-82ea-0522114c5ce3

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterMachine.lean:L324-L340
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.selected_digit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit
import Theorems.Thm_OAI_SingleFold_Packed_pack_digits

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma digit_zero (B t : ℕ) : digit B 0 t=0 := by simp [digit]
lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma digit_pack {B k : ℕ} (hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) (i : ℕ) :
    digit B (pack B k f) i=if i < k then f i else 0 := by
  induction k generalizing f i with
  | zero => simp [pack_zero,digit_zero]
  | succ k ih =>
    rw [pack_cons]
    cases i with
    | zero => simp [digit,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hf 0 (by omega)),zero_add]
      simpa only [digit, Nat.add_lt_add_iff_right] using ih (fun t ht=>hf (t+1) (by omega)) i

lemma bits_and (x y : ℕ) : Bits x y ↔ x&&&y=x := by
  rw [bits_testBit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i  <;> simp [hx,h i]
  · intro h i hi
    have hh := congrArg (fun n=>Nat.testBit n i) h
    simpa [Nat.testBit_and,hi] using hh
lemma bits_le {x y : ℕ} (h : Bits x y) : x ≤ y := by
  rw [←(bits_and x y).mp h]
  exact Nat.and_le_right
lemma bits_refl (x : ℕ) : Bits x x := fun _=>le_rfl
lemma bits_zero_left (x : ℕ) : Bits 0 x := by intro i; simp
lemma bits_one (x : ℕ) : Bits x 1 ↔ x ≤ 1 := by
  constructor
  · exact bits_le
  · intro h
    interval_cases x
    · exact bits_zero_left 1
    · exact bits_refl 1
lemma geometric {B : ℕ} (hB : 1 < B) (k : ℕ) : (B-1)*ones B k=B^k-1 := by
  induction k with
  | zero => simp [ones,pack_zero]
  | succ k ih =>
    change (B-1)*pack B (k+1) (fun _=>1)=B^(k+1)-1
    rw [pack_succ,mul_add,one_mul,pow_succ]
    change (B-1)*ones B k+(B-1)*B^k=B^k*B-1
    rw [ih]
    have hp := pow_pos (by omega : 0 < B) k
    nlinarith only [hp, hB, Nat.sub_add_cancel (by omega : 1 ≤ B), Nat.sub_add_cancel (by omega : 1 ≤ B^k), Nat.sub_add_cancel (show 1 ≤ B^k*B by exact Nat.mul_pos hp (by omega))]
lemma bits_ones {w k x : ℕ} (hw : 0 < w) :
    Bits x (ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k,digit (2^w) x t ≤ 1 := by
  simpa [bits_one] using bits_mask (x:=x) (k:=k) hw (Nat.one_lt_two_pow (by omega : w≠0))

lemma pack_sum {ι : Type} [Fintype ι] (B k : ℕ) (f : ι → ℕ → ℕ) :
    pack B k (fun t=>∑i,f i t)=∑i,pack B k (f i) := by
  simp only [pack, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma digit_sum {ι : Type} [Fintype ι] {B k : ℕ} (hB : 0 < B) (x : ι → ℕ)
    (hx : ∀i,x i < B^k) (hc : ∀t < k,∑i,digit B (x i) t < B) (t : ℕ) :
    digit B (∑i,x i) t=if t < k then ∑i,digit B (x i) t else 0 := by
  have he : (∑i,x i)=pack B k (fun t=>∑i,digit B (x i) t) := by
    rw [pack_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (pack_digits hB (hx i)).symm
  rw [he,digit_pack hB hc]

lemma bits_trans {x y z : ℕ} (hxy : Bits x y) (hyz : Bits y z) : Bits x z :=
  fun i=>(hxy i).trans (hyz i)
end SingleFold.Packed

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable [Fintype Q] [Fintype J]
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
omit [DecidableEq Q] [DecidableEq J] h in
lemma Cpos : 0 < baseC Q d := by simp [baseC]
lemma Bpos : 0 < v.B := by have := h.bound; have := (System.Cpos (Q:=Q) (d:=d)); omega
lemma Bfour : 4 ≤ v.B := by have := h.base; have := h.Bpos; omega
lemma Bgt : 1 < v.B := by have := h.Bfour; omega
lemma width : 0 < v.w := by
  by_contra hh
  have hw : v.w=0 := by omega
  have := h.power
  rw [hw,pow_zero] at this
  have := h.Bfour
  omega
lemma states_bound : 2*Fintype.card Q < v.B := by
  have := h.bound
  dsimp [baseC] at this
  omega
lemma mask_eq : v.mask=ones v.B v.k := by
  have he := h.mask
  rw [h.full,←geometric h.Bgt v.k] at he
  exact Nat.eq_of_mul_eq_mul_left (by have := h.Bgt; omega) he
end

section
variable (h : System M d v)
include h
lemma arc_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) v.mask := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left]; exact h.state_bits q
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi] using bits_trans hb.1 (h.state_bits q)
    · simpa only [arc,hi] using bits_trans hb.2.1 (h.state_bits q)
lemma arc_info (q : Q) (b : Bool) : arc M v q b < v.B^v.k ∧ ∀t < v.k,digit v.B (arc M v q b) t ≤ 1 := by
  have hh:=h.arc_bits q b
  rw [h.mask_eq,h.power] at hh
  rw [h.power]
  exact (bits_ones h.width).mp hh
end

variable (h : System M d v)
include h
lemma arc_digit_cap (t : ℕ) (ht : t < v.k) : (∑q,∑b : Bool,digit v.B (arc M v q b) t) < v.B := by
  have hc : (∑q,∑b : Bool,digit v.B (arc M v q b) t) ≤ 2*Fintype.card Q := by
    calc _ ≤ ∑q : Q,∑b : Bool,1 := Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun b _=>(h.arc_info q b).2 t ht))
         _ = _ := by simp; omega
  exact hc.trans_lt h.states_bound
lemma selected_digit (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑q,∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by
  have hx (a : Q×Bool) : (if P a.1 a.2 then arc M v a.1 a.2 else 0) < v.B^v.k := by
    split_ifs
    · exact (h.arc_info a.1 a.2).1
    · exact pow_pos h.Bpos _
  have hc : ∀u < v.k,(∑a : Q×Bool,digit v.B (if P a.1 a.2 then arc M v a.1 a.2 else 0) u) < v.B := by
    intro u hu
    apply lt_of_le_of_lt _ (h.arc_digit_cap u hu)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro b hb
    split_ifs <;> simp [digit_zero]
  have he:=digit_sum h.Bpos (fun a : Q×Bool=>if P a.1 a.2 then arc M v a.1 a.2 else 0) hx hc t
  simpa only [selected,Fintype.sum_prod_type,ite_eq_left ht,apply_ite (digit v.B) _,ite_apply,digit_zero] using he
end System
end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.selected_digit := @_root_.OAI.SingleFold.Counter.System.selected_digit
