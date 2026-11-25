-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.apply_eq_one_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:13.048899+00:00
-- url     : https://prove2.me/submissions/0b865fdd-8e2a-4dc5-b504-ae1aa57d622f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedChar_iff


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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {χ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) {u : Fˣ}
    (hu : ord (u : F) = 0) : χ u = 1 :=
  isUnramifiedChar_iff.1 h u hu
end GroundTheory.Automorphic.GodementSectionLocal
