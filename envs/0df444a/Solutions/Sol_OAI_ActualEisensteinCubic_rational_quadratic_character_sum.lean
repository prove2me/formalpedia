-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_quadratic_character_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:16.70068+00:00
-- url     : https://prove2.me/submissions/eda42071-24e6-4ae8-a472-2938cdb837ee

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) [NeZero m]
    (hodd : Odd m) :
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) = (m : ℂ) := by
  let ψ : AddChar (ZMod m) ℂ := ZMod.stdAddChar
  have htwo : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hodd)
  have hmulzero (b : ZMod m) : (2 : ZMod m) * b = 0 ↔ b = 0 := by
    simpa only [mul_zero] using
      (htwo.mul_right_inj (b := b) (c := (0 : ZMod m)))
  calc
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) =
        ∑ b : ZMod m, ∑ a : ZMod m, ψ (2*a*b-b^2) := by
      rw [Finset.sum_comm]
    _ = ∑ b : ZMod m, (if b = 0 then (m : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a : ZMod m, ψ (2*a*b-b^2)) =
            (∑ a : ZMod m, ψ (a*(2*b))) * ψ (-b^2) := by
          simp_rw [show ∀ a : ZMod m, 2*a*b-b^2 = a*(2*b)+(-b^2) from
            fun a => by ring, map_add_eq_mul]
          rw [Finset.sum_mul]
        _ = (if (2 : ZMod m)*b = 0 then (m : ℂ) else 0) * ψ (-b^2) := by
          rw [AddChar.sum_mulShift (2*b) (ZMod.isPrimitive_stdAddChar m)]
          simp
        _ = if b = 0 then (m : ℂ) else 0 := by
          simp only [hmulzero]
          split_ifs with h
          · subst b
            simp [ψ]
          · simp
    _ = (m : ℂ) := by simp
end OAI.ActualEisensteinCubic
