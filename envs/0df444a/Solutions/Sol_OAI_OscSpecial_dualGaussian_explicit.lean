-- Prove2me | solution 1 for OAI.OscSpecial.dualGaussian_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:13.760177+00:00
-- url     : https://prove2.me/submissions/5f1f41a2-1a87-4028-a652-02086892aefb

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_OscSpecial_r_pos
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_coefficient_re
import Theorems.Thm_OAI_OscSpecial_dualGaussian_inverseForm
import Theorems.Thm_OAI_OscSpecial_oscillatory_determinant
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
private theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRc : (R η a b : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring
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
theorem _root_.solution {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]
end OAI.OscSpecial
