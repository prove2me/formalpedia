-- Prove2me | solution 1 for GlobalTheory.GaussMarginal.map_ofLp_gaussProb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:11.245871+00:00
-- url     : https://prove2.me/submissions/3b1fc4f1-35d7-4e4a-baea-4978998005ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreserving
import Theorems.Thm_GlobalTheory_GaussMarginal_pi_withDensity_const
import Theorems.Thm_GlobalTheory_GaussMarginal_isProbabilityMeasure_complexGaussian_one
import Theorems.Thm_GlobalTheory_GaussMarginal_gaussProb_eq_complexGaussian
import Theorems.Thm_GlobalTheory_volume_preserving_ofLp_complex


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
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]
end GlobalTheory.GaussMarginal
