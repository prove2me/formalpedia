-- Prove2me | solution 1 for GroundTheory.LocalField.lowerIndex_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:22.889051+00:00
-- url     : https://prove2.me/submissions/ad9949c8-3594-40d3-ada5-94785077d34a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_top_iff

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
theorem _root_.solution {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : lowerIndex K L σ ≠ ⊤ :=
  fun h ↦ hσ (lowerIndex_eq_top_iff.mp h)
end GroundTheory.LocalField
