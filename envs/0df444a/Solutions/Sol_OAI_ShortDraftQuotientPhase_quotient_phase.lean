-- Prove2me | solution 1 for OAI.ShortDraftQuotientPhase.quotient_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:43.697717+00:00
-- url     : https://prove2.me/submissions/40da323f-c392-4dc9-b978-48a92e80f161

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
open OAI.ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]
namespace OAI.ShortDraftQuotientPhase
theorem _root_.solution (R : A → A → B) (G : A → B)
    (hRright : ∀ a b c, R a (b * c) = R a b * R a c)
    (hRsym : ∀ a b, R a b = R b a)
    (hRone : ∀ a, R a 1 = 1)
    (hRtwo : ∀ a b, R a b ^ 2 = 1)
    (hGmul : ∀ a b, G (a * b) = G a * G b * R a b)
    (hGone : G 1 = 1)
    (a b : A) :
    R a a * (G a)⁻¹ * G b * R a b = G (b * a⁻¹) := by
  have hRinv (x y : A) : R x y⁻¹ = (R x y)⁻¹ := by
    have h := hRright x y y⁻¹
    rw [mul_inv_cancel, hRone] at h
    have h' : R x y⁻¹ * R x y = 1 := by
      simpa [mul_comm] using h.symm
    exact (mul_eq_one_iff_eq_inv).mp h'
  have hRinv_eq (x y : A) : R x y⁻¹ = R x y := by
    rw [hRinv]
    have hsq : R x y * R x y = 1 := by
      simpa [pow_two] using hRtwo x y
    exact ((mul_eq_one_iff_eq_inv).mp hsq).symm
  have hGaInv : G a⁻¹ = R a a * (G a)⁻¹ := by
    have h := hGmul a a⁻¹
    rw [mul_inv_cancel, hGone, hRinv_eq] at h
    have ht : G a * G a⁻¹ = (R a a)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp h.symm
    have hsq : R a a * R a a = 1 := by
      simpa [pow_two] using hRtwo a a
    have hr : (R a a)⁻¹ = R a a :=
      ((mul_eq_one_iff_eq_inv).mp hsq).symm
    calc
      G a⁻¹ = (G a)⁻¹ * (G a * G a⁻¹) := by group
      _ = R a a * (G a)⁻¹ := by rw [ht, hr]; ac_rfl
  rw [hGmul b a⁻¹, hGaInv, hRinv_eq b a, hRsym b a]
  ac_rfl
end OAI.ShortDraftQuotientPhase
