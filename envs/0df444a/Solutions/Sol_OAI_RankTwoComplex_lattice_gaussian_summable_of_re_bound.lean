-- Prove2me | solution 1 for OAI.RankTwoComplex.lattice_gaussian_summable_of_re_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:19.484764+00:00
-- url     : https://prove2.me/submissions/ff4b7dcc-8059-4013-bc4f-a62a69bcca40

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoPoisson_real_gauss_summable
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
open OAI.RankTwoComplex
open Real
namespace OAI.RankTwoComplex
theorem _root_.solution (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hb := hbound z
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm := mul_le_mul_of_nonneg_left hb hpi
  have hexp : (-(Real.pi : ℂ) * F z).re ≤
      -Real.pi * eps * (z.1 : ℝ) ^ 2 +
      -Real.pi * eps * (z.2 : ℝ) ^ 2 := by
    simp [Complex.mul_re] at *
    nlinarith [hm]
  simpa only [Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)
end OAI.RankTwoComplex
