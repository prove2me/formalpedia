-- Prove2me | solution 1 for GroundTheory.LocalField.lintegral_multHaar_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:27.954061+00:00
-- url     : https://prove2.me/submissions/24091454-da99-45db-bec9-7c8d59585207

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
theorem _root_.solution (g : Kˣ → ℝ≥0∞) :
    ∫⁻ u, g u ∂multHaar K = ∑' k : ℤ, ∫⁻ u in ordShell K k, g u ∂multHaar K := by
  rw [← lintegral_iUnion measurableSet_ordShell pairwise_disjoint_ordShell, iUnion_ordShell,
    Measure.restrict_univ]
end GroundTheory.LocalField
