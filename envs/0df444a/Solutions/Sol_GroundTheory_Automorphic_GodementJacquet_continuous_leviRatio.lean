-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.continuous_leviRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:02.141533+00:00
-- url     : https://prove2.me/submissions/df766fdb-a9d7-4977-a12b-ee386219890f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable (β : Fin n → α)
variable {β}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution : Continuous (leviRatio (F := F) β) := by
  borelize F ↥(levi F n β) ↥(blockUpper F n β)
  show Continuous fun m : levi F n β =>
    (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  refine Continuous.div (LinearChart.continuous_leftModulus _) ?_ fun m =>
    (LinearChart.leftModulus_pos _ _).ne'
  exact (LinearChart.continuous_leftModulus _).comp
    (continuous_subtype_val.subtype_mk _ : Continuous fun m : levi F n β => leviIncl m)
end GroundTheory.Automorphic.GodementJacquet
