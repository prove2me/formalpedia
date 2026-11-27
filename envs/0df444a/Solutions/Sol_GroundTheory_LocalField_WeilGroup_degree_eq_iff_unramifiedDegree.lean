-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.degree_eq_iff_unramifiedDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:08.178801+00:00
-- url     : https://prove2.me/submissions/0fdb62f7-cbc1-49a2-902a-35caa199d834

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_restrictNormal_eq_frobenius_zpow_iff

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
theorem _root_.solution (σ : WeilGroup K Ω) (n : ℤ) :
    degree K Ω σ = Multiplicative.ofAdd n ↔
      unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [degree_eq_iff, restrictNormal_eq_frobenius_zpow_iff]
end GroundTheory.LocalField.WeilGroup
