-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.map_dirac_one_univ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:48.032951+00:00
-- url     : https://prove2.me/submissions/81ef9643-5d40-45a1-b336-b1aede105243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
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
namespace GlobalTheory.AutQuotCheck
theorem _root_.solution [MeasurableSpace G] :
    (((Measure.dirac (1 : G)).restrict Set.univ).map (cls Γ)) Set.univ = 1 := by
  rw [Measure.map_apply (measurable_cls Γ) MeasurableSet.univ]
  simp
end GlobalTheory.AutQuotCheck
