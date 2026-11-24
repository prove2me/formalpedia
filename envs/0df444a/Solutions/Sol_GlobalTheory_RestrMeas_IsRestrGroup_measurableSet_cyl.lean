-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsRestrGroup.measurableSet_cyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:42.502018+00:00
-- url     : https://prove2.me/submissions/48f9fe8d-2a46-4f53-b961-6a8b899a5842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_mem_levelAway
import Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_isOpen_levelAway

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
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
namespace GlobalTheory.RestrMeas
namespace IsRestrGroup
theorem _root_.solution (h : IsRestrGroup pa pf K) {S : Finset V} {A : ∀ w, Set (Ya w)}
    {B : ∀ v, Set (Yf v)} (hA : ∀ w, MeasurableSet (A w)) (hB : ∀ v ∈ S, MeasurableSet (B v)) :
    MeasurableSet (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) := by
  have : cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B =
      (⋂ w, pa w ⁻¹' A w) ∩ ((⋂ v ∈ S, pf v ⁻¹' B v) ∩ levelAway pf K S) := by
    ext x
    simp [mem_cyl, mem_levelAway]
  rw [this]
  exact (MeasurableSet.iInter fun w => (h.continuous_pa w).measurable (hA w)).inter
    ((S.measurableSet_biInter fun v hv => (h.continuous_pf v).measurable (hB v hv)).inter
      (h.isOpen_levelAway S).measurableSet)
end IsRestrGroup
end GlobalTheory.RestrMeas
