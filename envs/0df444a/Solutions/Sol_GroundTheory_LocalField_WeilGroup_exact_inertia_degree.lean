-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.exact_inertia_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:49.138806+00:00
-- url     : https://prove2.me/submissions/ae611cfb-c9e0-4d03-85ae-db61e1796225

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_WeilGroup_range_toGal
import Theorems.Thm_GroundTheory_LocalField_WeilGroup_degree_surjective
import Theorems.Thm_GroundTheory_LocalField_WeilGroup_inertia_eq_comap

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
variable (K Ω)
namespace GroundTheory.LocalField.WeilGroup
theorem _root_.solution :
    (degree K Ω).ker = inertia K Ω ∧ Function.Surjective (degree K Ω) ∧
      (inertia K Ω).map (toGal K Ω) = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  refine ⟨rfl, degree_surjective, ?_⟩
  rw [inertia_eq_comap, Subgroup.map_comap_eq, range_toGal]
  exact inf_of_le_right (fixingSubgroup_le_weilSubgroup K Ω)
end GroundTheory.LocalField.WeilGroup
