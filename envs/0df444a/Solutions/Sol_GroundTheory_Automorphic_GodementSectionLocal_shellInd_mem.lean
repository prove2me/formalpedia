-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.shellInd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:34.431428+00:00
-- url     : https://prove2.me/submissions/87c94530-7799-47b1-8d5b-1ee8c255f677

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isClopen_shellAt
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_shellAt_zero
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_indicator_mem_schwartzBruhat2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution : shellInd F ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (n := 0) (shellAt_zero (F := F) ▸ isClopen_shellAt 0)
    (fun _ hx ↦ hx.1) (IsLocallyConstant.const 1)
end GroundTheory.Automorphic.GodementSectionLocal
