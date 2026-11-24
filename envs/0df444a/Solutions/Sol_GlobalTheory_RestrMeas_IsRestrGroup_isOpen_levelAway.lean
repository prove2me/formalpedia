-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsRestrGroup.isOpen_levelAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:32.412701+00:00
-- url     : https://prove2.me/submissions/a11cb459-bbb1-42f6-8b6b-14d527389178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_mem_levelAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
namespace GlobalTheory.RestrMeas
namespace IsRestrGroup
theorem _root_.solution [IsTopologicalGroup X] (h : IsRestrGroup pa pf K) (S : Finset V) :
    IsOpen (levelAway pf K S : Set X) := by
  refine Subgroup.isOpen_mono (H₁ := levelAway pf K ∅) (fun x hx => ?_) ?_
  · exact mem_levelAway.2 fun v _ => mem_levelAway.1 hx v (by simp)
  · convert h.isOpen_level using 1
    ext x
    simp [mem_levelAway]
end IsRestrGroup
end GlobalTheory.RestrMeas
