-- Prove2me | solution 2 for OAI.SingleFold.Counter.System.halt_mask
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:09:17.815522+00:00
-- url     : https://prove2.me/submissions/7d9b7f6b-a20d-4999-be53-973de1c98edc

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterMachine.lean:L267-L279
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.System.halt_mask. The node keeps its source
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
end

section
variable (h : System M d v)
include h
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] h in
lemma arc_none (q : Q) (b : Bool) (he : dest M q b=none) : arc M v q b=0 := by
  cases hi : M.instr q <;> cases b <;> simp_all [dest,arc]
omit [Fintype J] [DecidableEq J] h in
lemma incoming_sum : (∑p,incoming M v p)=∑q,∑b : Bool,arc M v q b := by
  unfold incoming
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  cases he : dest M q b with
  | none => simp [System.arc_none (M:=M) (v:=v) q b he]
  | some p => simp
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
lemma transition_sum : v.mask=1+v.B*(∑q,∑b : Bool,arc M v q b) := by
  rw [←h.partition]
  calc
    _ = ∑q,((if q=M.start then 1 else 0)+v.B*incoming M v q) :=
      Finset.sum_congr rfl (fun q _=>h.transition q)
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,(System.incoming_sum (M:=M) (v:=v))]; simp
lemma halt_mask : v.state M.halt=v.last := by
  have h₁:=h.outgoing_sum
  have h₂:=h.transition_sum
  have h₃:=h.mask
  have h₄:=h.last
  have h₅ : 0 < v.H := by rw [h.full]; exact pow_pos h.Bpos _
  have h₆ : (v.B-1)*v.mask+v.mask=v.B*v.mask := by
    have hh : v.B-1+1=v.B := Nat.sub_add_cancel h.Bgt.le
    nlinarith
  have h₇ := congrArg (fun n=>v.B*n) h₁
  have h₈ : v.H-1+1=v.H := Nat.sub_add_cancel h₅
  have he : v.B*v.state M.halt=v.B*v.last := by nlinarith only [h₂,h₃,h₄,h₆,h₇,h₈]
  exact Nat.eq_of_mul_eq_mul_left h.Bpos he
end

variable (h : System M d v)
include h
end System
end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.System.halt_mask := @_root_.OAI.SingleFold.Counter.System.halt_mask
