-- Prove2me | solution 1 for GroundTheory.Global.filtrationSeparated_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:20.367575+00:00
-- url     : https://prove2.me/submissions/520a2d99-ba0c-42e0-8a31-83d14c1b8744

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_eq_zero_of_forall_mem_maximalIdeal_pow

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
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution : FiltrationSeparated (unitFiltration K) := by
  intro u hu
  have : (u : 𝒪[K]) - 1 = 0 := eq_zero_of_forall_mem_maximalIdeal_pow fun k ↦ hu k
  ext
  simpa [sub_eq_zero] using this
end GroundTheory.Global
