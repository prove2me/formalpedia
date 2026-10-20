-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.selected_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:12:52.427277+00:00
-- url     : https://prove2.me/submissions/7598ff01-81f1-4016-a7a3-ffebf74e137a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterMachine.lean:L341-L352
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.selected_bound. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_Counter_System_halt_mask

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_lt {B k : ℕ} (_hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) : pack B k f < B^k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ,pow_succ]
    have hi := ih (fun t ht=>hf t (by omega))
    have hh := hf k (by omega)
    nlinarith only [hi,hh,pow_pos _hB k]

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
lemma last_eq : v.last=v.B^(v.k-1) := by
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have he := h.last
  rw [h.full,hk,pow_succ'] at he
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
lemma mask_eq : v.mask=ones v.B v.k := by
  have he := h.mask
  rw [h.full,←geometric h.Bgt v.k] at he
  exact Nat.eq_of_mul_eq_mul_left (by have := h.Bgt; omega) he
end

section
variable (h : System M d v)
include h
lemma outgoing (q : Q) : v.state q=(if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b := by
  cases hi : M.instr q with
  | halt => have hq := (M.halt_iff q).mp hi; simp [hq,arc,(M.halt_iff M.halt).mpr rfl]
  | inc j p =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    simp [hq,arc,hi]
  | test j p0 pd =>
    have hq : q≠M.halt := by intro hh; have := (M.halt_iff q).mpr hh; rw [hi] at this; contradiction
    have hb := h.branch q
    rw [hi] at hb
    simpa [hq,arc,hi,add_comm] using hb.2.2.1.symm
lemma outgoing_sum : v.mask=v.state M.halt+∑q,∑b : Bool,arc M v q b := by
  rw [←h.partition]
  calc
    _ = ∑q,((if q=M.halt then v.state q else 0)+∑b : Bool,arc M v q b) :=
      Finset.sum_congr rfl (fun q _=>h.outgoing q)
    _ = _ := by rw [Finset.sum_add_distrib]; simp
end

variable (h : System M d v)
include h
lemma arcs_sum_eq : (∑q,∑b : Bool,arc M v q b)=ones v.B (v.k-1) := by
  have he:=h.outgoing_sum
  rw [h.mask_eq,h.halt_mask,h.last_eq] at he
  have hk : v.k=v.k-1+1 := by have := h.length; omega
  have hp : ones v.B v.k=ones v.B (v.k-1)+v.B^(v.k-1) := by
    nth_rw 1 [hk]
    simp only [ones,pack_succ,one_mul]
  rw [hp] at he
  omega
lemma selected_bound (P : Q → Bool → Prop) [DecidableRel P] : selected (M:=M) (v:=v) P < v.B^v.k := by
  have hl : selected (M:=M) (v:=v) P ≤ ∑q,∑b : Bool,arc M v q b := by
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro b hb
    split_ifs <;> simp
  have hb : ones v.B (v.k-1) ≤ ones v.B v.k := by
    have hk : v.k=v.k-1+1 := by have := h.length; omega
    conv_rhs => rw [hk,ones,pack_succ]
    exact Nat.le_add_right _ _
  exact hl.trans_lt ((h.arcs_sum_eq ▸ hb).trans_lt (pack_lt h.Bpos (fun _ _=>h.Bgt)))
end System
end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.selected_bound := @_root_.OAI.SingleFold.Counter.System.selected_bound
