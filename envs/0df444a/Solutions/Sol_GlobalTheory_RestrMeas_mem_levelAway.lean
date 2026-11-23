-- Prove2me | solution 1 for GlobalTheory.RestrMeas.mem_levelAway
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.903636+00:00
-- url     : https://prove2.me/submissions/a76571fc-b7ea-4bb9-a97f-f9a9e999e826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

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
omit [TopologicalSpace X] [∀ v, TopologicalSpace (Yf v)]
namespace GlobalTheory.RestrMeas
theorem _root_.solution {S : Finset V} {x : X} : x ∈ levelAway pf K S ↔ ∀ v ∉ S, pf v x ∈ K v := by
  simp [levelAway, Subgroup.mem_iInf]
end GlobalTheory.RestrMeas
