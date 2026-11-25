-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.isClopen_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:17.121448+00:00
-- url     : https://prove2.me/submissions/3610b48f-3555-438a-bf5b-3748d0f42883

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_coe_box
import Theorems.Thm_GroundTheory_LocalField_isClosed_valBall
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall


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
theorem _root_.solution (n : ℤ) : IsClopen (box F n : Set (Fin 2 → F)) := by
  rw [coe_box]
  exact ⟨isClosed_set_pi fun _ _ ↦ isClosed_valBall n,
    isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n⟩
end GroundTheory.Automorphic.GodementSectionLocal
