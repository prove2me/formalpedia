-- Prove2me | solution 1 for GroundTheory.Global.distribHaarChar_finiteSingleUnits_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:05:32.481146+00:00
-- url     : https://prove2.me/submissions/5111718b-b64f-4bb2-8c94-00d77ed4b2b7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_measure_eq_card_mul_measure_ker
import Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles_ne_zero
import Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles_ne_top
import Theorems.Thm_GroundTheory_Global_residueAt_surjective
import Theorems.Thm_GroundTheory_Global_finiteSingleUnits_smul_eq_ker
import Theorems.Thm_GroundTheory_Global_isOpen_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletionIntegers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (hϖ0 : (ϖ : v.adicCompletion K) ≠ 0) :
    distribHaarChar 𝔸ᶠ[K] (finiteSingleUnits v (Units.mk0 _ hϖ0)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  have hcount := measure_eq_card_mul_measure_ker (finiteAdeleMeasure K)
    (integralFiniteAdeles (𝓞 K) K).toAddSubgroup (residueAt v) (residueAt_surjective v)
    (by
      rw [← finiteSingleUnits_smul_eq_ker hϖ hϖ0]
      exact isOpen_integralFiniteAdeles.smul _)
  rw [natCard_residueField_adicCompletionIntegers] at hcount
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := finiteAdeleMeasure K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_zero K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_top K) ?_
  rw [finiteSingleUnits_smul_eq_ker hϖ hϖ0]
  change _ = _ * finiteAdeleMeasure K ((integralFiniteAdeles (𝓞 K) K).toAddSubgroup : Set 𝔸ᶠ[K])
  rw [hcount, ENNReal.coe_inv hN0, ENNReal.coe_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hN0) (ENNReal.natCast_ne_top _), one_mul]
end GroundTheory.Global
