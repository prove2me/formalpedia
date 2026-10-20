-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.test_values
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:18:12.085195+00:00
-- url     : https://prove2.me/submissions/f0b5d2ca-6b05-47f9-867e-a0e50b3961cc

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterRecords.lean:L249-L267
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.test_values. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_selected_digit
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
lemma width : 0 < v.w := by
  by_contra hh
  have hw : v.w=0 := by omega
  have := h.power
  rw [hw,pow_zero] at this
  have := h.Bfour
  omega
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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SingleFold.Packed
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
end

section
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable
lemma select_test (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    digit v.B (selected (M:=M) (v:=v) P) t=
      (if P q true then digit v.B (v.decBranch q) t else 0)+
      (if P q false then digit v.B (v.zeroBranch q) t else 0) := by
  rw [h.selected_at_state P t ht q hs]
  simp [arc,hi]
lemma test_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    (∀z,digit v.B (incoming M v z) t=
      (if z=pd then digit v.B (v.decBranch q) t else 0)+
      (if z=p0 then digit v.B (v.zeroBranch q) t else 0)) ∧
    (∀i,digit v.B (increments M v i) t=0) ∧
    (∀i,digit v.B (decrements M v i) t=if i=j then digit v.B (v.decBranch q) t else 0) := by
  constructor
  · intro z
    rw [(System.incoming_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [dest,hi,eq_comm]
  constructor
  · intro i
    rw [(System.inc_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [hi]
  · intro i
    rw [(System.dec_selected (M:=M) (v:=v)),h.select_test _ t ht q hs j p0 pd hi]
    simp [hi,eq_comm]
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


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.test_values := @_root_.OAI.SingleFold.Counter.System.test_values
