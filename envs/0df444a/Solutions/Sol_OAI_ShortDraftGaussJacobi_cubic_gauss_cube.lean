-- Prove2me | solution 1 for OAI.ShortDraftGaussJacobi.cubic_gauss_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:16.723989+00:00
-- url     : https://prove2.me/submissions/39f6bf91-ea4d-404a-a412-f81300c7767d

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
open OAI.ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.ShortDraftGaussJacobi
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : ℂ) * jacobiSum χ χ := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  have hneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (n := 3) (by decide)
      (by simpa [horder] using (pow_orderOf_eq_one χ))
  have hj := jacobiSum_mul_nontrivial hχ2 ψ
  have hg := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ hψ
  simp only [horder, Nat.reduceSub, pow_two] at hg
  rw [hneg, one_mul] at hg
  calc
    gaussSum χ ψ ^ 3 = gaussSum χ ψ * (gaussSum χ ψ * gaussSum χ ψ) := by ring
    _ = gaussSum χ ψ * (gaussSum (χ * χ) ψ * jacobiSum χ χ) := by rw [hj]
    _ = (Fintype.card F : ℂ) * jacobiSum χ χ := by rw [← mul_assoc, hg]
end OAI.ShortDraftGaussJacobi
