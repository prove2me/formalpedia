-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.measurable_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:08.95486+00:00
-- url     : https://prove2.me/submissions/fbf8a1b4-facd-4408-b4a3-a25a255e7bdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume

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
theorem _root_.solution [MeasurableSpace G] :
    Measurable (_root_.GlobalTheory.AutQuotCheck.cls Γ) := fun _ hs => hs
end _root_.GlobalTheory.AutQuotCheck
end GlobalTheory.AutQuotCheck
