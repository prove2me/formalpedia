-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.finite_lattice_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:20:11.465577+00:00
-- url     : https://prove2.me/submissions/0ddb94e3-d41a-4c66-bd5a-da1f8a77e124

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_coordinate_squares
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ShortDraftLatticeCount
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith [sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring
end OAI.ShortDraftLatticeCount
