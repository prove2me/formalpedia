-- Prove2me | solution 1 for OAI.RankTwoPoisson.real_gauss_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:51.254213+00:00
-- url     : https://prove2.me/submissions/f02ff7fd-452f-436f-848f-6e0a314683f4

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (cg_summable htc).norm
  simpa [cg, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h
end OAI.RankTwoPoisson
