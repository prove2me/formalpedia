-- Prove2me | solution 1 for OAI.EisensteinGaussianPrefactor.eta_times_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:49.84502+00:00
-- url     : https://prove2.me/submissions/a848f053-ba97-4bcd-9699-e3b59b280060

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_EisensteinGaussianPrefactor_sqrt_product

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
    η * (1 / Real.sqrt (η*q)) *
      (1 / Real.sqrt (3*(η*q)/4)) =
      2 / (Real.sqrt 3 * q) := by
  have ht : 0 < η*q := mul_pos hη hq
  have hsqrt : Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4) =
      Real.sqrt 3 * (η*q) / 2 := sqrt_product (η*q) ht.le
  have hne1 : Real.sqrt (η*q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hne2 : Real.sqrt (3*(η*q)/4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hne3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    η * (1 / Real.sqrt (η*q)) *
        (1 / Real.sqrt (3*(η*q)/4)) =
        η / (Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4)) := by ring
    _ = η / (Real.sqrt 3 * (η*q) / 2) := by rw [hsqrt]
    _ = 2 / (Real.sqrt 3 * q) := by
      field_simp
end OAI.EisensteinGaussianPrefactor
