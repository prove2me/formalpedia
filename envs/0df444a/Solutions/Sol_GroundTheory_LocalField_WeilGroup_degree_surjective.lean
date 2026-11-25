-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.degree_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:41.493072+00:00
-- url     : https://prove2.me/submissions/1f74b12a-7c7c-478e-9ac2-a89c268bc76b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_exists_restrictNormal_eq_frobenius_zpow

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
theorem _root_.solution : Function.Surjective (degree K Ω) := by
  intro n
  obtain ⟨σ, hσ⟩ := exists_restrictNormal_eq_frobenius_zpow K Ω n.toAdd
  exact ⟨mk σ (mem_weilSubgroup_iff.2 ⟨_, hσ⟩), (degree_eq_iff _ n.toAdd).2 hσ⟩
end GroundTheory.LocalField.WeilGroup
