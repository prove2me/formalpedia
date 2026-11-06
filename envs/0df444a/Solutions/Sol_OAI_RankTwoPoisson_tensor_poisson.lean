-- Prove2me | solution 1 for OAI.RankTwoPoisson.tensor_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:28:02.578298+00:00
-- url     : https://prove2.me/submissions/3b4e8fd1-5d91-4754-9e15-f6f9dd8f38b3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_RankTwoPoisson_schwartz_int_norm_summable
import Theorems.Thm_OAI_RankTwoPoisson_schwartz_int_poisson

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
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution (f g : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
      ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) := by
  calc
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
        (∑' m : ℤ, f (m : ℝ)) * (∑' n : ℤ, g (n : ℝ)) :=
      (tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable f) (schwartz_int_norm_summable g)).symm
    _ = (∑' m : ℤ, (𝓕 f) (m : ℝ)) * (∑' n : ℤ, (𝓕 g) (n : ℝ)) :=
      congrArg₂ (· * ·) (schwartz_int_poisson f) (schwartz_int_poisson g)
    _ = ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) :=
      tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable (𝓕 f))
        (schwartz_int_norm_summable (𝓕 g))
  rfl
end OAI.RankTwoPoisson
