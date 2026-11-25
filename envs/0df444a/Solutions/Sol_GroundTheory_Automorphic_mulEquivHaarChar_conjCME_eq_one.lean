-- Prove2me | solution 1 for GroundTheory.Automorphic.mulEquivHaarChar_conjCME_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:56.16719+00:00
-- url     : https://prove2.me/submissions/9180f740-fbd4-4708-a397-cc6b1179148e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_pow
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_inv
import Theorems.Thm_GroundTheory_Automorphic_exists_bound_mulEquivHaarChar_conjCME

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
theorem _root_.solution {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G}
    (hk : k ∈ K) : mulEquivHaarChar (conjCME k) = 1 := by
  obtain ⟨B, hB⟩ := exists_bound_mulEquivHaarChar_conjCME hK fun k hk => K.inv_mem hk
  have hle : ∀ a ∈ K, mulEquivHaarChar (conjCME a) ≤ 1 := by
    intro a ha
    by_contra hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hlt)
    have := hB (a ^ n) (K.pow_mem ha n)
    rw [mulEquivHaarChar_conjCME_pow] at this
    exact absurd this (not_le.2 hn)
  have h1 := hle k hk
  have h2 := hle k⁻¹ (K.inv_mem hk)
  have h3 := mulEquivHaarChar_conjCME_inv k
  refine le_antisymm h1 ?_
  by_contra hlt
  have hlt' := not_le.1 hlt
  have : mulEquivHaarChar (conjCME k⁻¹) * mulEquivHaarChar (conjCME k) < 1 :=
    calc mulEquivHaarChar (conjCME k⁻¹) * mulEquivHaarChar (conjCME k)
        ≤ 1 * mulEquivHaarChar (conjCME k) := by gcongr
      _ < 1 := by rwa [one_mul]
  rw [h3] at this
  exact lt_irrefl _ this
end GroundTheory.Automorphic
