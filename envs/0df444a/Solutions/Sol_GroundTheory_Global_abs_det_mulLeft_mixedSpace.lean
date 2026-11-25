-- Prove2me | solution 1 for GroundTheory.Global.abs_det_mulLeft_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:09.53353+00:00
-- url     : https://prove2.me/submissions/13d09c97-79d7-479a-947b-a1167eddbf85

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Theorems.Thm_GroundTheory_Global_det_mulLeft_mixedSpace

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
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (c : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ c)| = mixedEmbedding.norm c := by
  rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]
end GroundTheory.Global
