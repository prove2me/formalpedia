-- Prove2me | solution 1 for GlobalTheory.Doubling.continuous_of_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:58.06579+00:00
-- url     : https://prove2.me/submissions/4e85051f-ce37-48b4-a8d3-6d7866d8c730

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

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
namespace GlobalTheory.Doubling
theorem _root_.solution (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {X : Type} [TopologicalSpace X] {f : G → X}
    (hf : Continuous fun x : P × K => f (x.1 * x.2)) : Continuous f := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : G × K ≃ₜ G × K :=
    { toFun := fun x => (x.1 * x.2, x.2), invFun := fun x => (x.1 * (x.2 : G)⁻¹, x.2)
      left_inv := fun x => by simp, right_inv := fun x => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  have hc : IsClosedMap fun x : P × K => (x.1 : G) * x.2 :=
    (isClosedMap_fst_of_compactSpace.comp e.isClosedMap).comp
      (hP.isClosedEmbedding_subtypeVal.prodMap (Topology.IsClosedEmbedding.id (X := K))).isClosedMap
  exact (hc.isQuotientMap (by fun_prop) fun g => by
    obtain ⟨p, k, hk, rfl⟩ := h g; exact ⟨(p, ⟨k, hk⟩), rfl⟩).continuous_iff.2 hf
end GlobalTheory.Doubling
