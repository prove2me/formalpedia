-- Prove2me | solution 1 for OAI.SingleFold.Counter.System.halt_mask
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:39:05.517354+00:00
-- url     : https://prove2.me/submissions/e136836d-5931-4a02-aa5e-4b7e94c6ffb4

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


theorem solution : v.state M.halt=v.last := by
  classical
  -- arcs out of q sum to state q unless q is halt
  have harc : ∀ q, (∑ b : Bool, arc M v q b) = if q = M.halt then 0 else v.state q := by
    intro q
    have hb := h.branch q
    have hh := M.halt_iff q
    simp only [Fintype.sum_bool]
    unfold arc
    revert hb hh
    cases M.instr q <;> intro hb hh <;> simp only at hb ⊢
    · simp [hh.mp rfl]
    · simp at hh; simp [hh]
    · simp at hh; simp [hh]; try omega
  -- arcs with no destination vanish
  have hdest : ∀ q b, (∑ p, if dest M q b = some p then arc M v q b else 0) = arc M v q b := by
    intro q b
    cases hd : dest M q b with
    | none =>
      simp only [reduceCtorEq, if_false, Finset.sum_const_zero]
      unfold dest at hd; unfold arc
      revert hd
      cases M.instr q <;> cases b <;> simp
    | some p0 =>
      simp
  have hinc : (∑ p, incoming M v p) = v.mask - v.state M.halt := by
    unfold incoming
    rw [Finset.sum_comm]
    have hswap : ∀ q, (∑ p, ∑ b : Bool, if dest M q b = some p then arc M v q b else 0) =
        ∑ b : Bool, arc M v q b := by
      intro q; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun b _ => hdest q b)
    simp_rw [hswap, harc]
    rw [← h.partition, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun q => q = M.halt) v.state
    rw [Finset.filter_eq' Finset.univ M.halt] at this
    simp only [Finset.mem_univ, if_true, Finset.sum_singleton] at this
    omega
  have hsum : v.mask = 1 + v.B * (v.mask - v.state M.halt) := by
    have := Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => h.transition q)
    rw [h.partition, Finset.sum_add_distrib, ← Finset.mul_sum, hinc] at this
    simpa [Finset.sum_ite_eq'] using this
  have hle : v.state M.halt ≤ v.mask := by
    rw [← h.partition]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hm := h.mask
  have hl := h.last
  have hB : 0 < v.B := by have := h.bound; omega
  have hH : 1 ≤ v.H := by rw [h.full]; exact Nat.one_le_pow _ _ hB
  have key : v.B * v.state M.halt = v.B * v.last := by
    rw [hl]
    have e1 : v.B * (v.mask - v.state M.halt) + v.B * v.state M.halt = v.B * v.mask := by
      rw [← mul_add, Nat.sub_add_cancel hle]
    have e2 : (v.B - 1) * v.mask + v.mask = v.B * v.mask := by
      obtain ⟨c, hc⟩ : ∃ c, v.B = c + 1 := ⟨v.B - 1, by omega⟩
      rw [hc]; simp; ring
    omega
  exact Nat.eq_of_mul_eq_mul_left hB key

