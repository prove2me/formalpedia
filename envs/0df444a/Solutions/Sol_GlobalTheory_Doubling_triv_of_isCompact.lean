-- Prove2me | solution 1 for GlobalTheory.Doubling.triv_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.370492+00:00
-- url     : https://prove2.me/submissions/fb9ee773-8e53-4e50-97d1-0a30d54eb7ca

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_hom_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
variable {δ K}
variable [TopologicalSpace G] [IsTopologicalGroup G]
omit [IsTopologicalGroup G]
namespace GlobalTheory.Doubling
theorem _root_.solution (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (p : P)
    (hp : (p : G) ∈ K) : δ p = 1 := by
  obtain ⟨C, hC⟩ := ((hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hδ).bddAbove
  have key : ∀ q : P, (q : G) ∈ K → δ q ≤ 1 := fun q hq => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    exact absurd (hC ⟨q ^ n, pow_mem hq n, map_pow δ q n⟩) (not_le.2 hn)
  refine le_antisymm (key p hp) ?_
  have := key p⁻¹ (inv_mem hp)
  rwa [map_inv, inv_le_one₀ (hom_pos δ p)] at this
end GlobalTheory.Doubling
