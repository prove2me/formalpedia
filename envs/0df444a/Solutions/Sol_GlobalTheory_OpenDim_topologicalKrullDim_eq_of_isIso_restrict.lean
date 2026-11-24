-- Prove2me | solution 1 for GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:58.474858+00:00
-- url     : https://prove2.me/submissions/069299f7-79fd-4b9c-9bdb-5a73963a4355

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
import Theorems.Thm_GlobalTheory_OpenDim_topologicalKrullDim_open
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim
namespace GlobalTheory.OpenDim
theorem _root_.solution : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  intro F _ W W' _ _ p q h hp hq _ U hU hiso
  have hsurj : Function.Surjective (h ∣_ U) := (h ∣_ U).surjective
  have e₁ : topologicalKrullDim (U : Set W) = topologicalKrullDim (h ⁻¹ᵁ U) := by
    refine topologicalKrullDim_eq_of_isEmbedding ((h ∣_ U) ≫ U.ι).isOpenEmbedding.isEmbedding ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
  have e₂ : topologicalKrullDim ((h ⁻¹ᵁ U : W'.Opens) : Set W') =
      topologicalKrullDim (h ⁻¹ᵁ U) :=
    topologicalKrullDim_eq_of_isEmbedding (h ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding
      (Scheme.Opens.range_ι _)
  have hne : ((h ⁻¹ᵁ U : W'.Opens) : Set W').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨y, -⟩ := hsurj ⟨u, hu⟩
    exact ⟨(h ⁻¹ᵁ U).ι y, by rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩⟩
  rw [← topologicalKrullDim_open F q (h ⁻¹ᵁ U) hne, ← topologicalKrullDim_open F p U hU, e₁, e₂]
end GlobalTheory.OpenDim
