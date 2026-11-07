-- Prove2me | solution 1 for OAI.OscSpecial.prefactor_eq_real_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:14.470393+00:00
-- url     : https://prove2.me/submissions/fa9b8ae1-0c8b-4da3-9faa-6f2d1da95df8

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_OscSpecial_r_pos
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
open Filter Real Asymptotics
open ActualEisensteinCubic
namespace OscSpecial
end OscSpecial
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring
private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]
open scoped Topology
open Filter
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]
end OAI.OscSpecial
