-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.exists_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:51.740632+00:00
-- url     : https://prove2.me/submissions/b2c3ea80-2b7b-4e82-947f-778da8915abd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_WeilGroup_degree_surjective

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
theorem _root_.solution : ∃ φ : WeilGroup K Ω, degree K Ω φ = Multiplicative.ofAdd 1 :=
  degree_surjective _
end GroundTheory.LocalField.WeilGroup
