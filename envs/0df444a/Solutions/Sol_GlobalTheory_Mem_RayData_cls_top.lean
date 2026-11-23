-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.cls_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.408798+00:00
-- url     : https://prove2.me/submissions/6c6be867-9591-488f-8e01-32a4eba9265a

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
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution : D.cls ⊤ = 1 := by
  rw [← Ideal.one_eq_top]
  exact D.cls_one
end GlobalTheory.Mem.RayData
