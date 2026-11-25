-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.boxInd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:29.075308+00:00
-- url     : https://prove2.me/submissions/9cd61ff4-fe78-4ef2-aab2-840b09d886ac

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isClopen_box
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
theorem _root_.solution (n : ℤ) : boxInd F n ∈ schwartzBruhat2 F :=
  indicator_mem_schwartzBruhat2 (isClopen_box n) le_rfl (IsLocallyConstant.const 1)
end GroundTheory.Automorphic.GodementSectionLocal
