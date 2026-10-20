-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.decode
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:22:10.925476+00:00
-- url     : https://prove2.me/submissions/25a7d997-8a8d-4beb-ae99-53dfce6f30c9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterRecords.lean:L287-L350
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.decode. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_halt_mask
import Theorems.Thm_OAI_SingleFold_Counter_System_selected_digit
import Theorems.Thm_OAI_SingleFold_Counter_System_test_choice
import Theorems.Thm_OAI_SingleFold_Counter_System_test_values
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

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
end SingleFold.Packed

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma run_succ (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1)=next M (run M d t) :=
  Function.iterate_succ_apply' _ _ _
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
lemma last_eq : v.last=v.B^(v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := h.last
  rw [h.full,hk,pow_succ'] at he
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
end

section
variable (h : System M d v)
include h
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
lemma digit_init {B a x : ℕ} (hB : 0 < B) (ha : a < B) :
    digit B (a+B*x) 0=a ∧ ∀t,digit B (a+B*x) (t+1)=digit B x t := by
  constructor
  · simp [digit,Nat.mod_eq_of_lt ha]
  · intro t
    rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt ha,zero_add]
    rfl
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System
variable (h : System M d v)
include h
omit [Fintype J] [DecidableEq J] h in
lemma incoming_selected (p : Q) : incoming M v p=selected (M:=M) (v:=v) (fun q b=>dest M q b=some p) := rfl
attribute [local instance] Classical.propDecidable
omit [Fintype J] [DecidableEq Q] h in
lemma inc_selected (j : J) : increments M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .inc i _ => i=j ∧ b=false | _=>False) := by
  unfold increments selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
omit [Fintype J] [DecidableEq Q] h in
lemma dec_selected (j : J) : decrements M v j=selected (M:=M) (v:=v)
    (fun q b=>match M.instr q with | .test i _ _ => i=j ∧ b=true | _=>False) := by
  unfold decrements selected
  apply Finset.sum_congr rfl
  intro q hq
  cases hi : M.instr q <;> simp [hi,arc]
lemma state_initial (q : Q) : digit v.B (v.state q) 0=if q=M.start then 1 else 0 := by
  rw [h.transition q]
  apply (digit_init h.Bpos _).1
  split_ifs <;> have := h.Bgt <;> omega
lemma state_step (q : Q) (t : ℕ) : digit v.B (v.state q) (t+1)=digit v.B (incoming M v q) t := by
  rw [h.transition q]
  apply (digit_init h.Bpos _).2
  split_ifs <;> have := h.Bgt <;> omega
end System
end SingleFold.Counter

namespace SingleFold.Packed
lemma digit_power {B T t : ℕ} (hB : 1 < B) (ht : t < T+1) : digit B (B^T) t=if t=T then 1 else 0 := by
  have he : B^T=pack B (T+1) (fun u=>if u=T then 1 else 0) := by simp [pack]
  have hc : ∀u < T+1,(if u=T then 1 else 0) < B := by intro u hu; split_ifs <;> omega
  rw [he,digit_pack (by omega) hc,ite_eq_left ht]
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
lemma arc_state_bits (q : Q) (b : Bool) : Packed.Bits (arc M v q b) (v.state q) := by
  cases hi : M.instr q with
  | halt => cases b <;> simp [arc,hi,bits_zero_left]
  | inc j p => cases b <;> simp [arc,hi,bits_zero_left,bits_refl]
  | test j p0 pd =>
    have hb:=h.branch q
    rw [hi] at hb
    cases b
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.1
    · simpa only [arc,hi,Bits,Packed.Bits] using hb.2.1
lemma arc_digit_le (q : Q) (b : Bool) (t : ℕ) : digit v.B (arc M v q b) t ≤ digit v.B (v.state q) t := by
  have hh:=h.arc_state_bits q b
  rw [h.power] at *
  exact bits_le ((bits_blocks h.width _ _).mp hh t)
lemma selected_at_state (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by
  rw [h.selected_digit P t ht]
  apply Finset.sum_eq_single q
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro b hb
    have hzero : digit v.B (arc M v p b) t=0 := by have hh:=h.arc_digit_le p b t; rw [hs p,ite_eq_right hpq] at hh; omega
    simp [hzero]
  · simp
lemma halt_digit (t : ℕ) (ht : t < v.k) : digit v.B (v.state M.halt) t=if t=v.k-1 then 1 else 0 := by
  rw [h.halt_mask,h.last_eq]
  apply digit_power h.Bgt
  have := h.length
  omega
end

section
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
lemma select_inc (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p : Q) (hi : M.instr q=.inc j p) :
    digit v.B (selected (M:=M) (v:=v) P) t=if P q false then 1 else 0 := by
  rw [h.selected_at_state P t ht q hs]
  simp [arc,hi,hs q,digit_zero]
lemma inc_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p : Q) (hi : M.instr q=.inc j p) :
    (∀z,digit v.B (incoming M v z) t=if z=p then 1 else 0) ∧
    (∀i,digit v.B (increments M v i) t=if i=j then 1 else 0) ∧
    (∀i,digit v.B (decrements M v i) t=0) := by
  constructor
  · intro z
    rw [(System.incoming_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [dest,hi,eq_comm]
  constructor
  · intro i
    rw [(System.inc_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [hi,eq_comm]
  · intro i
    rw [(System.dec_selected (M:=M) (v:=v)),h.select_inc _ t ht q hs j p hi]
    simp [hi]
lemma decode (t : ℕ) (ht : t < v.k) :
    (∀q,digit v.B (v.state q) t=if q=(run M d t).state then 1 else 0) ∧
    (∀j,digit v.B (v.counter (some j)) t=(run M d t).value j) := by
  induction t with
  | zero => exact ⟨h.state_initial,fun j=>(h.counter_update j).1⟩
  | succ t ih =>
    have ht' : t < v.k-1 := by omega
    have ht0 : t < v.k := by omega
    rcases ih ht0 with ⟨hs,hr⟩
    have hnh : (run M d t).state≠M.halt := by
      intro hh
      have hd:=h.halt_digit t ht0
      rw [hh] at hs
      rw [hs M.halt,ite_eq_left rfl,ite_eq_right (by omega)] at hd
      omega
    cases hi : M.instr (run M d t).state with
    | halt => exact False.elim (hnh ((M.halt_iff _).mp hi))
    | inc j p =>
      have hv:=h.inc_values t ht0 _ hs j p hi
      have hn : run M d (t+1)=⟨p,Function.update (run M d t).value j ((run M d t).value j+1)⟩ := by
        rw [run_succ,next,hi]
      rw [hn]
      constructor
      · intro q; exact (h.state_step q t).trans (hv.1 q)
      · intro i
        have hu:=(h.counter_update i).2 t ht'
        rw [hv.2.1 i,hv.2.2 i,hr i,add_zero] at hu
        by_cases hij : i=j
        · subst i; simpa using hu
        · simpa [hij,Function.update_of_ne hij] using hu
    | test j p0 pd =>
      have hv:=h.test_values t ht0 _ hs j p0 pd hi
      have hc:=h.test_choice t ht' _ hs j p0 pd hi
      rw [hr j] at hc
      by_cases hz : (run M d t).value j=0
      · simp only [ite_eq_left hz] at hc
        have hn : run M d (t+1)=⟨p0,(run M d t).value⟩ := by rw [run_succ]; simp [next,hi,hz]
        rw [hn]
        constructor
        · intro q
          rw [h.state_step,hv.1,hc.1,hc.2]
          simp
        · intro i
          have hu:=(h.counter_update i).2 t ht'
          rw [hv.2.1 i,hv.2.2 i,hc.2,hr i] at hu
          simpa using hu
      · simp only [ite_eq_right hz] at hc
        have hn : run M d (t+1)=⟨pd,Function.update (run M d t).value j ((run M d t).value j-1)⟩ := by
          rw [run_succ]; simp [next,hi,hz]
        rw [hn]
        constructor
        · intro q
          rw [h.state_step,hv.1,hc.1,hc.2]
          simp
        · intro i
          have hu:=(h.counter_update i).2 t ht'
          rw [hv.2.1 i,hv.2.2 i,hc.2,hr i,add_zero] at hu
          by_cases hij : i=j
          · subst i
            simp only [ite_true] at hu
            change _=(Function.update (run M d t).value j ((run M d t).value j-1)) j
            simp only [Function.update_self]
            omega
          · simpa [hij,Function.update_of_ne hij] using hu
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


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.decode := @_root_.OAI.SingleFold.Counter.System.decode
