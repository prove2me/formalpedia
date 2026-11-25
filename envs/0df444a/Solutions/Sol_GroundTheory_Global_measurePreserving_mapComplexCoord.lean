-- Prove2me | solution 1 for GroundTheory.Global.measurePreserving_mapComplexCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:21.973499+00:00
-- url     : https://prove2.me/submissions/faace73c-420a-42a1-b298-e45fe729c6d6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_det_mapComplexCoord

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
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (a : ℂ ≃L[ℝ] ℂ)
    (ha : |LinearMap.det (a : ℂ →ₗ[ℝ] ℂ)| = 2) :
    MeasurePreserving (mapComplexCoord K a) (selfDualMeasure K) volume := by
  refine ⟨(mapComplexCoord K a).continuous.measurable, ?_⟩
  have hd := det_mapComplexCoord K a
  have hne : LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) ≠ 0 := by
    rw [hd]
    refine pow_ne_zero _ fun h => ?_
    rw [h, abs_zero] at ha
    norm_num at ha
  have hmap : Measure.map (mapComplexCoord K a) (volume : Measure (mixedSpace K)) =
      ENNReal.ofReal |(LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K))⁻¹| •
        (volume : Measure (mixedSpace K)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  rw [selfDualMeasure, Measure.map_smul, hmap, smul_smul, hd, abs_inv, abs_pow, ha,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]
end GroundTheory.Global
