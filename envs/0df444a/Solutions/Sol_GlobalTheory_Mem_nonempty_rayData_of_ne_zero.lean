-- Prove2me | solution 1 for GlobalTheory.Mem.nonempty_rayData_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:16.810361+00:00
-- url     : https://prove2.me/submissions/0e6adeff-78af-4015-997f-7078b42185c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
namespace GlobalTheory.Mem
theorem _root_.solution (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : M ≠ 0) : Nonempty (RayData K M) := ⟨rayData K M hM⟩
end GlobalTheory.Mem
