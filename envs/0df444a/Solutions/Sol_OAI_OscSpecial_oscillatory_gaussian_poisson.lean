-- Prove2me | solution 1 for OAI.OscSpecial.oscillatory_gaussian_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:25.015101+00:00
-- url     : https://prove2.me/submissions/7670679c-8692-4855-ad9d-1d4eff269dd6

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_OscSpecial_binary_gaussian_poisson_real_det
import Theorems.Thm_OAI_OscSpecial_coefficient_re
import Theorems.Thm_OAI_OscSpecial_oscillatory_determinant
import Theorems.Thm_OAI_OscSpecial_real_positive_definite


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
open Filter Real Asymptotics
open ActualEisensteinCubic
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)
end OAI.OscSpecial
