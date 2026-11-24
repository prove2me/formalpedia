-- Prove2me | solution 1 for GlobalTheory.T.map_restrict_isHaar_of_open_product_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:17.408805+00:00
-- url     : https://prove2.me/submissions/a9cc4d00-132c-4d74-a0bc-76bc2f8935e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompactStatement
import Theorems.Thm_GlobalTheory_ChainOnto_map_restrict_isHaar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  first | exact @GlobalTheory.ChainOnto.map_restrict_isHaar | exact GlobalTheory.ChainOnto.map_restrict_isHaar | (intros; apply GlobalTheory.ChainOnto.map_restrict_isHaar <;> assumption)
end _root_.GlobalTheory.T
