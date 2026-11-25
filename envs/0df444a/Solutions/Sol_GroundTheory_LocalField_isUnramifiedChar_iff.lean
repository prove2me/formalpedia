-- Prove2me | solution 1 for GroundTheory.LocalField.isUnramifiedChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:39.236349+00:00
-- url     : https://prove2.me/submissions/1c44e144-a6fc-4290-9710-8d8fec4324b7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar

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
variable (χ : Kˣ →* ℂˣ)
variable {χ}
namespace GroundTheory.LocalField
theorem _root_.solution : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by
  refine ⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩
  exact h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)
end GroundTheory.LocalField
