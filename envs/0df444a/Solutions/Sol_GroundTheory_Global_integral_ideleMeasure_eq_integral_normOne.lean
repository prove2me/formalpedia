-- Prove2me | solution 1 for GroundTheory.Global.integral_ideleMeasure_eq_integral_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:49.292901+00:00
-- url     : https://prove2.me/submissions/b67e8628-9f5e-4b81-898d-3b6a1392a5ca

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Theorems.Thm_GroundTheory_Global_map_normOneSplitting_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (w : InfinitePlace K) {f : IdeleGroup K → E}
    (hf : Integrable f (ideleMeasure K)) :
    ∫ x, f x ∂ideleMeasure K =
      ∫ t, ∫ u, f ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K ∂posRealMeasure := by
  have hcomp : (fun p ↦ f ((normOneSplitting w).symm p)) ∘ (normOneSplitting w) = f :=
    funext fun x ↦ congrArg f ((normOneSplitting w).symm_apply_apply x)
  have h1 : ∫ x, f x ∂ideleMeasure K =
      ∫ p, f ((normOneSplitting w).symm p) ∂(normOneMeasure K).prod posRealMeasure := by
    rw [← map_normOneSplitting_eq_prod w]
    change _ = ∫ p, f ((normOneSplitting w).symm p)
      ∂Measure.map (normOneSplitting w).toHomeomorph.toMeasurableEquiv (ideleMeasure K)
    rw [integral_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv]
    exact congrArg (fun g ↦ ∫ x, g x ∂ideleMeasure K) hcomp.symm
  rw [h1, integral_prod_symm]
  · rfl
  · rw [← map_normOneSplitting_eq_prod w]
    exact (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv
      (fun p ↦ f ((normOneSplitting w).symm p))).2 (by convert hf using 1; exact hcomp)
end GroundTheory.Global
