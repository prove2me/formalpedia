-- Prove2me | solution 1 for OAI.EisensteinGaussianPrefactor.complex_eta_times_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:57.574328+00:00
-- url     : https://prove2.me/submissions/14659926-6e6b-4d4a-aab2-8449061fd4dd

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_EisensteinGaussianPrefactor_eta_times_prefactor

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
open OAI.EisensteinGaussianPrefactor
namespace OAI.EisensteinGaussianPrefactor
theorem _root_.solution (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    (η : ℂ) *
      (1 / ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ)) *
      (1 / (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ))) =
      ((2 / (Real.sqrt 3 * q) : ℝ) : ℂ) := by
  have ht : 0 ≤ η*q := (mul_pos hη hq).le
  have hs : 0 ≤ 3*(η*q)/4 := by positivity
  have hpow1 : ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
      (Real.sqrt (η*q) : ℂ) := by
    calc
      ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
          ((η*q : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ)) := by norm_num
      _ = (((η*q) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow ht (1/2 : ℝ)).symm
      _ = (Real.sqrt (η*q) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 : (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
      (Real.sqrt (3*(η*q)/4) : ℂ) := by
    calc
      (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
          (((3*(η*q)/4 : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ))) := by norm_num
      _ = (((3*(η*q)/4) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow hs (1/2 : ℝ)).symm
      _ = (Real.sqrt (3*(η*q)/4) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  rw [hpow1, hpow2]
  exact_mod_cast eta_times_prefactor η q hη hq
end OAI.EisensteinGaussianPrefactor
