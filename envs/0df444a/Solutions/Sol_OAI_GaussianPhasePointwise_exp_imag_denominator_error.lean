-- Prove2me | solution 1 for OAI.GaussianPhasePointwise.exp_imag_denominator_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:47.245662+00:00
-- url     : https://prove2.me/submissions/4fcab811-e0d6-4bb9-a9c1-d871fc05877d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_GaussianPhasePointwise_exp_imag_diff_le
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
open OAI.GaussianPhasePointwise
namespace OAI.GaussianPhasePointwise
theorem _root_.solution (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]
end OAI.GaussianPhasePointwise
