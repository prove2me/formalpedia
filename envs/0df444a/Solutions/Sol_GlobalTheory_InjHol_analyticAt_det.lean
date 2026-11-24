-- Prove2me | solution 1 for GlobalTheory.InjHol.analyticAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:40.723487+00:00
-- url     : https://prove2.me/submissions/70f71267-5b91-4a6b-ae2f-9fb51bf3c296

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z => LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  first
  | exact @_root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det
  | exact _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det
  | (apply _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det ..)
end GlobalTheory.InjHol
