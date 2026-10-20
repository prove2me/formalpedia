-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.test_choice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:20:16.615611+00:00
-- url     : https://prove2.me/submissions/deab2654-0c18-4fef-b58d-4d7e5b66901f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterRecords.lean:L268-L286
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.test_choice. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_counter_update
import Theorems.Thm_OAI_SingleFold_Counter_System_test_values
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit
import Theorems.Thm_OAI_SingleFold_Packed_pack_digits

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma testBit_digit (w x t j : ℕ) :
    (digit (2^w) x t).testBit j=(decide (j < w) && x.testBit (w*t+j)) := by
  unfold digit
  rw [Nat.testBit_mod_two_pow,←pow_mul]
  congr 1
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.div_div_eq_div_mul,←pow_add]

lemma bits_blocks {w : ℕ} (hw : 0 < w) (x y : ℕ) :
    Bits x y ↔ ∀t, Bits (digit (2^w) x t) (digit (2^w) y t) := by
  simp only [bits_testBit,testBit_digit,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h t j hj
    exact ⟨hj.1,h _ hj.2⟩
  · intro h i hi
    have hh := h (i/w) (i%w) ⟨Nat.mod_lt i hw, by simpa [Nat.div_add_mod] using hi⟩
    simpa [Nat.div_add_mod] using hh.2

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
lemma pack_add (B k : ℕ) (f g : ℕ → ℕ) :
    pack B k (fun t=>f t+g t)=pack B k f+pack B k g := by simp [pack,add_mul,Finset.sum_add_distrib]
lemma pack_mul (B k c : ℕ) (f : ℕ → ℕ) :
    pack B k (fun t=>c*f t)=c*pack B k f := by simp [pack,Finset.mul_sum,mul_assoc]
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
lemma bits_zero_right (x : ℕ) : Bits x 0 ↔ x=0 := by
  exact ⟨fun h=>Nat.eq_zero_of_le_zero (bits_le h),fun h=>h ▸ bits_refl 0⟩
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

lemma bits_trans {x y z : ℕ} (hxy : Bits x y) (hyz : Bits y z) : Bits x z :=
  fun i=>(hxy i).trans (hyz i)
lemma pack_congr {B k : ℕ} {f g : ℕ → ℕ} (h : ∀t < k,f t=g t) : pack B k f=pack B k g := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]
end SingleFold.Packed

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterRecords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SingleFold.Packed
lemma digit_add {B k x y : ℕ} (hB : 0 < B) (hx : x < B^k) (hy : y < B^k)
    (hc : ∀t < k,digit B x t+digit B y t < B) (t : ℕ) (ht : t < k) :
    digit B (x+y) t=digit B x t+digit B y t := by
  have he : x+y=pack B k (fun t=>digit B x t+digit B y t) := by
    rw [pack_add,pack_digits hB hx,pack_digits hB hy]
  rw [he,digit_pack hB hc,ite_eq_left ht]
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
end System
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
lemma test_partition (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) (t : ℕ) (ht : t < v.k) :
    digit v.B (v.zeroBranch q) t+digit v.B (v.decBranch q) t=digit v.B (v.state q) t := by
  have hz:=h.arc_info q false
  have hn:=h.arc_info q true
  simp only [arc,hi] at hz hn
  have hb:=h.branch q
  rw [hi] at hb
  rw [←hb.2.2.1]
  symm
  apply digit_add h.Bpos hz.1 hn.1 _ t ht
  intro u hu
  have := hz.2 u hu
  have := hn.2 u hu
  have := h.Bfour
  omega
lemma complement_pack (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    v.complement q=pack v.B v.k (fun t=>1-digit v.B (v.zeroBranch q) t) := by
  have hz:=h.arc_info q false
  simp only [arc,hi] at hz
  have hb:=h.branch q
  rw [hi] at hb
  have he : pack v.B v.k (digit v.B (v.zeroBranch q))+pack v.B v.k (fun t=>1-digit v.B (v.zeroBranch q) t)=ones v.B v.k := by
    rw [←pack_add]
    apply pack_congr
    intro t ht
    exact Nat.add_sub_of_le (hz.2 t ht)
  rw [pack_digits h.Bpos hz.1,←h.mask_eq] at he
  omega
lemma zero_branch_forces (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd)
    (t : ℕ) (ht : t < v.k) (hz : digit v.B (v.zeroBranch q) t=1) : digit v.B (v.counter (some j)) t=0 := by
  have hb:=h.zero_test q
  rw [hi] at hb
  change Packed.Bits _ _ at hb
  rw [h.complement_pack q j p0 pd hi,←pack_mul] at hb
  have hc : ∀u < v.k,(v.B-1)*(1-digit v.B (v.zeroBranch q) u) < v.B := by
    intro u hu
    have hh : 1-digit v.B (v.zeroBranch q) u ≤ 1 := Nat.sub_le _ _
    have := h.Bpos
    nlinarith only [hh,this,Nat.sub_le v.B 1,Nat.sub_lt this (by omega : 0 < 1)]
  have hb' : Packed.Bits (digit v.B (v.counter (some j)) t)
      (digit v.B (pack v.B v.k (fun u=>(v.B-1)*(1-digit v.B (v.zeroBranch q) u))) t) := by
    rw [h.power] at hb ⊢
    exact (bits_blocks h.width _ _).mp hb t
  rw [digit_pack h.Bpos hc,ite_eq_left ht,hz,Nat.sub_self,mul_zero] at hb'
  exact (bits_zero_right _).mp hb'
end

section
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
lemma test_choice (t : ℕ) (ht : t < v.k-1) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    digit v.B (v.zeroBranch q) t=(if digit v.B (v.counter (some j)) t=0 then 1 else 0) ∧
    digit v.B (v.decBranch q) t=(if digit v.B (v.counter (some j)) t=0 then 0 else 1) := by
  have ht' : t < v.k := by omega
  have hp:=h.test_partition q j p0 pd hi t ht'
  rw [hs q,ite_eq_left rfl] at hp
  have hv:=h.test_values t ht' q hs j p0 pd hi
  have hu:=(h.counter_update j).2 t ht
  rw [hv.2.1 j,hv.2.2 j,ite_eq_left rfl,add_zero] at hu
  by_cases hz : digit v.B (v.counter (some j)) t=0
  · simp only [ite_eq_left hz]
    omega
  · have hn : digit v.B (v.zeroBranch q) t≠1 := by
      intro hh
      exact hz (h.zero_branch_forces q j p0 pd hi t ht' hh)
    simp only [ite_eq_right hz]
    omega
end

variable (h : System M d v)
include h
end System

end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.test_choice := @_root_.OAI.SingleFold.Counter.System.test_choice
