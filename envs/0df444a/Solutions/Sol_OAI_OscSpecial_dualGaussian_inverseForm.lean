-- Prove2me | solution 1 for OAI.OscSpecial.dualGaussian_inverseForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:58.06723+00:00
-- url     : https://prove2.me/submissions/73458ea1-b826-4130-8003-68fe38e339f1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
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
namespace GaussianMoment
end GaussianMoment
namespace ActualEisensteinCubic
section
open ShortDraftLatticeCount
end
end ActualEisensteinCubic
open ActualEisensteinCubic
namespace RationalPrimeExtraction
end RationalPrimeExtraction
namespace OscSpecial
private theorem schur_eq_real_det_div {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    RankTwoComplex.schur a b d = (R : ℂ) / a := by
  unfold RankTwoComplex.schur
  rw [← hdet]
  field_simp [ha]
end OscSpecial
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
theorem _root_.solution {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hdet : a * d - b ^ 2 = (R : ℂ)) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * inverseForm a b d R z) := by
  unfold RankTwoComplex.dualGaussian
  rw [← Complex.exp_add]
  congr 1
  rw [schur_eq_real_det_div ha hdet]
  dsimp [inverseForm]
  have hdet0 : a * d - b ^ 2 ≠ 0 := by rw [hdet]; exact_mod_cast hR
  rw [← hdet]
  field_simp [ha, hdet0] ; ring
end OAI.OscSpecial
