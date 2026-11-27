-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.denseRange_toGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:47.233972+00:00
-- url     : https://prove2.me/submissions/7780ee01-efdf-423e-8224-a201903bca34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_dense_weilSubgroup
import Theorems.Thm_GroundTheory_LocalField_WeilGroup_range_toGal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
open GroundTheory.LocalField.WeilGroup
variable {K Ω}
namespace GroundTheory.LocalField.WeilGroup
theorem _root_.solution : DenseRange (toGal K Ω) := by
  have h := dense_weilSubgroup K Ω
  rw [← range_toGal, MonoidHom.coe_range] at h
  exact h
end GroundTheory.LocalField.WeilGroup
