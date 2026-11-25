-- Prove2me | solution 1 for GroundTheory.LocalField.hasSum_setIntegral_ordShell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:25.212311+00:00
-- url     : https://prove2.me/submissions/e724389e-0d4e-402d-9dfb-b11a118fb559

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_pairwise_disjoint_ordShell
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Kˣ → E} (hF : Integrable F (multHaar K)) :
    HasSum (fun k : ℤ => ∫ u in ordShell K k, F u ∂multHaar K) (∫ u, F u ∂multHaar K) := by
  have := hasSum_integral_iUnion (μ := multHaar K) (measurableSet_ordShell (K := K))
    (pairwise_disjoint_ordShell (K := K)) (by rw [iUnion_ordShell]; exact hF.integrableOn)
  rwa [iUnion_ordShell, Measure.restrict_univ] at this
end GroundTheory.LocalField
