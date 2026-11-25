-- Prove2me | solution 1 for GroundTheory.Global.det_mapComplexCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:48.652051+00:00
-- url     : https://prove2.me/submissions/e1f3df52-3c11-4f01-b6ff-937dec4d33f7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier

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
theorem _root_.solution (a : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.det (a : ℂ →ₗ[ℝ] ℂ) ^ nrComplexPlaces K := by
  have : (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.prodMap LinearMap.id
        (LinearMap.pi fun w => (a : ℂ →ₗ[ℝ] ℂ) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_pi,
    Finset.prod_const, Finset.card_univ]
end GroundTheory.Global
