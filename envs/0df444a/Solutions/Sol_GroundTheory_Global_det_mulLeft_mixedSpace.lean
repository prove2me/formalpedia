-- Prove2me | solution 1 for GroundTheory.Global.det_mulLeft_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:27.92475+00:00
-- url     : https://prove2.me/submissions/8f74f401-aeca-4a98-9792-4a2ec558771d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling

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
    LinearMap.det (LinearMap.mulLeft ℝ c) =
      (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  have h : LinearMap.mulLeft ℝ c = LinearMap.prodMap
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.1 w) ∘ₗ LinearMap.proj w)
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.2 w) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ ↦ rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ LinearMap.det_mulLeft _
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
end GroundTheory.Global
