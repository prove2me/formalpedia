-- Prove2me | solution 1 for OAI.GaussianMoment.real_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:47.035935+00:00
-- url     : https://prove2.me/submissions/0a14b17a-cf53-4696-8ed6-93edacf3718c

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_GaussianMoment_realGauss_cast
import Theorems.Thm_OAI_EisensteinAbelFiber_shifted_gaussian_mass
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open OAI.GaussianMoment
open scoped Topology
open Filter
namespace OAI.GaussianMoment
theorem _root_.solution :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe
end OAI.GaussianMoment
