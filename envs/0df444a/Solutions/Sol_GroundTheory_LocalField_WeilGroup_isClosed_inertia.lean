-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.isClosed_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:56.111459+00:00
-- url     : https://prove2.me/submissions/39091ac3-4218-4ef7-8c31-c18bda9d4d7a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs

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
theorem _root_.solution : IsClosed (inertia K Ω : Set (WeilGroup K Ω)) :=
  OpenSubgroup.isClosed ⟨inertia K Ω, isOpen_inertia⟩
end GroundTheory.LocalField.WeilGroup
