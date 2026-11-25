-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.modPow_units_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:09.904145+00:00
-- url     : https://prove2.me/submissions/8916d5af-6ce9-4f7e-b483-a3c77bb7dd20

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_zpow


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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (u : Fˣ) (s : ℂ) :
    modPow (u : F) s = ((residueCard F : ℂ) ^ (-s)) ^ ord (u : F) :=
  modulus_cpow_eq_zpow u s
end GroundTheory.Automorphic.GodementSectionLocal
