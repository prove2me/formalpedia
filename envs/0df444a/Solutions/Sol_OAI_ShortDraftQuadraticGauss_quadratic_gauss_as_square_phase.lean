-- Prove2me | solution 1 for OAI.ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:36.283904+00:00
-- url     : https://prove2.me/submissions/fc90ac90-15d6-47f4-a6ca-46934ae16889

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
namespace OAI.ShortDraftQuadraticGauss
theorem _root_.solution (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    have hterm : (∑ x ∈ Finset.univ with x ^ 2 = y, ψ (x ^ 2)) =
        (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
      rw [Finset.sum_congr rfl (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx])]
      simp
    exact hterm
  have hcount (y : F) :
      (#{x : F | x ^ 2 = y}.toFinset : ℂ) =
        (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ y : F, ψ y) = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  simp only [one_mul, hzero, add_zero]
  rfl
end OAI.ShortDraftQuadraticGauss
