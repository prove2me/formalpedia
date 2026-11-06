-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_unit_eq_one_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:16.400242+00:00
-- url     : https://prove2.me/submissions/7a9e893f-f856-4f3a-81b1-b031db66d074

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_cubicChar_neg_one
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega_eq_one_of_card_mod_nine
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) (u : Oˣ) :
    cubicChar P hgood (Ideal.Quotient.mk P (u : O)) = 1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hone : cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 :=
    cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  have hminus : cubicChar P hgood (-1 : O ⧸ P) = 1 :=
    A3_cubicChar_neg_one P hgood
  have hneg (x : O) :
      cubicChar P hgood (Ideal.Quotient.mk P (-x)) =
        cubicChar P hgood (Ideal.Quotient.mk P x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one, hminus, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using hminus
  · rw [h, hη]
    exact hone
  · rw [h, Units.val_neg, hneg, hη]
    exact hone
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
    norm_num
  · rcases h with h | h
    · rw [h, Units.val_neg, hneg, Units.val_pow_eq_pow_val, hη, map_pow, map_pow, hone]
      norm_num
    · simp at h
end OAI.ActualEisensteinCubic
