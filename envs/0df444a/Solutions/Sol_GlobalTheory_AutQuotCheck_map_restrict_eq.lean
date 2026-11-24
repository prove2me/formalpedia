-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.map_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:28:49.205941+00:00
-- url     : https://prove2.me/submissions/af306c83-55c2-4fa0-ae0b-7da08e5e0751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
import Theorems.Thm_GlobalTheory_AutQuotCheck_cls_smul
import Theorems.Thm_GlobalTheory_AutQuotCheck_measurable_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.AutQuotCheck
variable {G : Type} [Group G] (Γ : Subgroup G)
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] (Γ : Subgroup G)
namespace GlobalTheory.AutQuotCheck
namespace _root_.GlobalTheory.AutQuotCheck
theorem _root_.solution [MeasurableSpace G] [Countable Γ]
    [MeasurableConstSMul Γ G] (μ : Measure G) [SMulInvariantMeasure Γ G μ] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' μ) :
    (μ.restrict F).map (_root_.GlobalTheory.AutQuotCheck.cls Γ) =
      (μ.restrict F').map (_root_.GlobalTheory.AutQuotCheck.cls Γ) := by
  ext s hs
  have hA := _root_.GlobalTheory.AutQuotCheck.measurable_cls Γ hs
  rw [Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h.measure_set_eq h' hA fun γ => ?_
  ext x
  simp only [Set.mem_preimage, _root_.GlobalTheory.AutQuotCheck.cls_smul]
end _root_.GlobalTheory.AutQuotCheck
end GlobalTheory.AutQuotCheck
