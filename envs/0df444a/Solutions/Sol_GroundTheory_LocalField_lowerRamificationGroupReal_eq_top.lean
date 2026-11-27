-- Prove2me | solution 1 for GroundTheory.LocalField.lowerRamificationGroupReal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:23.336433+00:00
-- url     : https://prove2.me/submissions/51492c13-a6e2-4b45-94f7-8bda0722806a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_eq_top


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
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {t : ℝ} (ht : t ≤ -1) :
    lowerRamificationGroupReal K L t = ⊤ :=
  lowerRamificationGroup_eq_top K L (Int.ceil_le.mpr (by push_cast; exact ht))
end GroundTheory.LocalField
