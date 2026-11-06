-- Prove2me | solution 1 for OAI.EisensteinGaussianPrefactor.sqrt_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:21.739884+00:00
-- url     : https://prove2.me/submissions/597fedce-5d42-4785-9609-24636436ea59

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit

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
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (3*t/4) =
      Real.sqrt 3 * t / 2 := by
  have h3 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have harg : 3*t/4 = (3/4:ℝ)*t := by ring
  rw [harg, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4), h3]
  calc
    Real.sqrt t * (Real.sqrt 3 / 2 * Real.sqrt t) =
        Real.sqrt 3 / 2 * (Real.sqrt t)^2 := by ring
    _ = Real.sqrt 3 * t / 2 := by rw [Real.sq_sqrt ht]; ring
end OAI.EisensteinGaussianPrefactor
