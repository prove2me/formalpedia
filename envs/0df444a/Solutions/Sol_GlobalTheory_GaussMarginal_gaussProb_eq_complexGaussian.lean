-- Prove2me | solution 1 for GlobalTheory.GaussMarginal.gaussProb_eq_complexGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:57.678167+00:00
-- url     : https://prove2.me/submissions/a1ecac12-4a91-4e79-8f6d-349618f1ef01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreserving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.GaussMarginal
open Real
namespace GlobalTheory.GaussMarginal
theorem _root_.solution (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]
end GlobalTheory.GaussMarginal
