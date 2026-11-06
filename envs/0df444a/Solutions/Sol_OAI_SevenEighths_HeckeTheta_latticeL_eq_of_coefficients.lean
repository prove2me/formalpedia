-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.latticeL_eq_of_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:50:35.313343+00:00
-- url     : https://prove2.me/submissions/d9133247-5855-4fc3-9c0b-531897525d87

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FamilySeries
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_eq_of_coefficients_right
import Theorems.Thm_OAI_SevenEighths_Continuation_product_identity_on_halfPlane
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_periodicCoeff_zero
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_regularizedLatticeL_differentiableAt
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_regularizedLatticeL_eq
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.HeckeTheta.periodicCoeff_zero
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) : latticeL w s = latticeL v s := by
  have hwa : AnalyticOnNhd ℂ (regularizedLatticeL w) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt w
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hva : AnalyticOnNhd ℂ (regularizedLatticeL v) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt v
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hident := Continuation.product_identity_on_halfPlane 0 1
    (regularizedLatticeL w) (fun _ => 1) (regularizedLatticeL v)
    hwa analyticOnNhd_const hva (by
      intro z hz
      have hz' : 1 < z.re := by simpa using hz
      have hz₀ : z ≠ 0 := by intro h; norm_num [h] at hz'
      have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz'
      simp only [mul_one, regularizedLatticeL_eq w hz₀ hz₁,
        regularizedLatticeL_eq v hz₀ hz₁,
        latticeL_eq_of_coefficients_right w v hcoeff hz']) hs
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs
  simp only [mul_one, regularizedLatticeL_eq w hs₀ hs₁,
    regularizedLatticeL_eq v hs₀ hs₁] at hident
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs₁) hident
end OAI.SevenEighths.HeckeTheta
