-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.exists_mem_box_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:26.190835+00:00
-- url     : https://prove2.me/submissions/63b291e3-f9a7-4a8f-9f57-6772995e0178

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mem_box
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone


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
theorem _root_.solution (x : Fin 2 → F) : ∃ m : ℕ, x ∈ box F (-(m : ℤ)) := by
  obtain ⟨a, ha⟩ := exists_mem_valBall_neg_nat (x 0)
  obtain ⟨b, hb⟩ := exists_mem_valBall_neg_nat (x 1)
  refine ⟨max a b, mem_box.2 fun i ↦ ?_⟩
  fin_cases i
  · exact valBall_antitone (by omega) ha
  · exact valBall_antitone (by omega) hb
end GroundTheory.Automorphic.GodementSectionLocal
