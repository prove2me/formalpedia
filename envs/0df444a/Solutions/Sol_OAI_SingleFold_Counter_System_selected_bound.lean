-- Prove2me | solution 1 for OAI.SingleFold.Counter.System.selected_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:18:12.746131+00:00
-- url     : https://prove2.me/submissions/83355542-617b-498c-bb34-db716e77cbab

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

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h


theorem solution (P : Q → Bool → Prop) [DecidableRel P] : selected (M:=M) (v:=v) P < v.B^v.k := by
  have harc : ∀ q, (∑ b : Bool, if P q b then arc M v q b else 0) ≤ v.state q := by
    intro q
    have hb := h.branch q
    have le1 : (∑ b : Bool, if P q b then arc M v q b else 0) ≤ ∑ b : Bool, arc M v q b :=
      Finset.sum_le_sum (fun b _ => by split <;> omega)
    refine le_trans le1 ?_
    simp only [Fintype.sum_bool]
    unfold arc
    revert hb
    cases M.instr q <;> intro hb <;> simp only at hb ⊢ <;> omega
  have h1 : selected (M:=M) (v:=v) P ≤ v.mask := by
    unfold selected; rw [← h.partition]
    exact Finset.sum_le_sum (fun q _ => harc q)
  have hB : 2 ≤ v.B := by have := h.bound; unfold baseC at this; omega
  have hm := h.mask
  have hH := h.full
  have hpos : 0 < v.B ^ v.k := by positivity
  have : v.mask ≤ (v.B - 1) * v.mask := Nat.le_mul_of_pos_left _ (by omega)
  omega

