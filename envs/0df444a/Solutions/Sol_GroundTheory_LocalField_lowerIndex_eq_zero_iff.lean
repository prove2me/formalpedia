-- Prove2me | solution 1 for GroundTheory.LocalField.lowerIndex_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:59:54.564046+00:00
-- url     : https://prove2.me/submissions/da8b03bb-4eab-491f-ab7b-a24b0438b15a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_one_le_lowerIndex_iff

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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {σ : L ≃ₐ[K] L} :
    lowerIndex K L σ = 0 ↔ σ ∉ lowerRamificationGroup K L 0 := by
  rw [← one_le_lowerIndex_iff, not_le, Order.lt_one_iff]
end GroundTheory.LocalField
