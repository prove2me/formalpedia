-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.unramifiedDegree_toGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:06.259888+00:00
-- url     : https://prove2.me/submissions/e828dd14-7f04-4521-aa17-a9aaaca54e9e

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
theorem _root_.solution (σ : WeilGroup K Ω) :
    unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (((degree K Ω σ).toAdd : ℤ) : ℤ̂) :=
  (restrictNormal_eq_frobenius_zpow_iff _ _).1 (restrictNormal_toGal σ)
end GroundTheory.LocalField.WeilGroup
