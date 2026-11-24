-- Prove2me | solution 1 for GlobalTheory.T.compact_covered_by_open_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:32.426997+00:00
-- url     : https://prove2.me/submissions/a061f16a-b365-40df-b1ab-b96743c89245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosets
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosetsStatement
import Theorems.Thm_GlobalTheory_compact_finite_leftCoset_reps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  first | exact @GlobalTheory.compact_finite_leftCoset_reps | exact GlobalTheory.compact_finite_leftCoset_reps | (intros; apply GlobalTheory.compact_finite_leftCoset_reps <;> assumption)
end _root_.GlobalTheory.T
