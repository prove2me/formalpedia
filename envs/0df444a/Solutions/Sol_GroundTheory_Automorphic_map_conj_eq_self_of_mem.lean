-- Prove2me | solution 1 for GroundTheory.Automorphic.map_conj_eq_self_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:17.983316+00:00
-- url     : https://prove2.me/submissions/c7525749-cde2-4daf-a367-52f290edde00

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (conjCME k) = μ := by
  have e := mulEquivHaarChar_smul_map μ (conjCME k)
  rwa [mulEquivHaarChar_conjCME_eq_one hK hk, one_smul] at e
end GroundTheory.Automorphic
