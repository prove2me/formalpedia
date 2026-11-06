-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_units_agree_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:16.959453+00:00
-- url     : https://prove2.me/submissions/15f4b54c-d77f-449a-ae01-706417ae88cc

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega_agree_of_card_mod_nine
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_cubicChar_neg_one
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
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9)
    (u : Oˣ) :
    cubicChar P hP (Ideal.Quotient.mk P (u : O)) =
      cubicChar Q hQ (Ideal.Quotient.mk Q (u : O)) := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω := cubicChar_omega_agree_of_card_mod_nine P Q hP hQ hcard
  have hnegP := A3_cubicChar_neg_one P hP
  have hnegQ := A3_cubicChar_neg_one Q hQ
  have hminus (R : Ideal O) [R.IsMaximal] (hR : lambda ∉ R) (x : O) :
      cubicChar R hR (Ideal.Quotient.mk R (-x)) =
        cubicChar R hR (Ideal.Quotient.mk R x) := by
    have hx : -x = (-1 : O) * x := by ring
    rw [hx, map_mul, map_mul, map_neg, map_one,
      A3_cubicChar_neg_one R hR, one_mul]
  simp only [List.mem_cons] at hu
  rcases hu with h | h | h | h | h | h
  · rw [h]
    simp
  · rw [h]
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      hnegP.trans hnegQ.symm
  · rw [h, hη]
    exact hω
  · rw [h, Units.val_neg, hminus P hP, hminus Q hQ, hη]
    exact hω
  · rw [h, Units.val_pow_eq_pow_val, hη, map_pow, map_pow,
      map_pow, map_pow, hω]
  · rcases h with h | h
    · rw [h, Units.val_neg, hminus P hP, hminus Q hQ,
        Units.val_pow_eq_pow_val, hη, map_pow, map_pow, map_pow, map_pow, hω]
    · simp at h
end OAI.ActualEisensteinCubic
