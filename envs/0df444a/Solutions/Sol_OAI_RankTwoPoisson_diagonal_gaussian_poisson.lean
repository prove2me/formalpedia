-- Prove2me | solution 1 for OAI.RankTwoPoisson.diagonal_gaussian_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:27.489802+00:00
-- url     : https://prove2.me/submissions/a1d4b69a-83f9-4f86-adce-9735f2f26558

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic
end GaussianAbelPartition
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace GaussianFiberEquiv
open ActualEisensteinCubic
end GaussianFiberEquiv
namespace RankTwoPoisson
open Real
private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)
private theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha
private theorem cg_poisson {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cg a n) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg a⁻¹ n := by
  simpa only [cg, div_eq_mul_inv, neg_mul, mul_assoc] using
    Complex.tsum_exp_neg_mul_int_sq ha
end RankTwoPoisson
end
end OAI
end

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
theorem _root_.solution {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hai : 0 < (a⁻¹).re) (hbi : 0 < (b⁻¹).re) :
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
  calc
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
        (∑' m : ℤ, cg a m) * (∑' n : ℤ, cg b n) :=
      (tsum_mul_tsum_of_summable_norm (cg_summable ha).norm (cg_summable hb).norm).symm
    _ = ((1 / a ^ (1 / 2 : ℂ)) * ∑' m : ℤ, cg a⁻¹ m) *
        ((1 / b ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg b⁻¹ n) := by
      rw [cg_poisson ha, cg_poisson hb]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
      rw [← tsum_mul_tsum_of_summable_norm (cg_summable hai).norm (cg_summable hbi).norm]
      ring
end OAI.RankTwoPoisson
