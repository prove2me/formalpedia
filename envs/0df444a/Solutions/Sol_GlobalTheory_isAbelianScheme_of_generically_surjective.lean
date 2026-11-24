-- Prove2me | solution 1 for GlobalTheory.isAbelianScheme_of_generically_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:34.58054+00:00
-- url     : https://prove2.me/submissions/742dedf7-efa0-4df0-aee5-4a1f738fa41a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
import Theorems.Thm_GlobalTheory_surjective_of_generic_fibre_subset_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by
  intro V K _ _ _ _ _ _ B G _ _ hB hG ψ h
  have := hB.proper
  have := hG.smooth
  have := hG.separated
  have hw : ψ.left ≫ G.hom = B.hom := Over.w ψ
  have : IsProper (ψ.left ≫ G.hom) := hw ▸ hB.proper
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have : Surjective ψ.left := surjective_of_generic_fibre_subset_range ψ.left G.hom h
  have : UniversallyClosed G.hom := UniversallyClosed.of_comp_surjective ψ.left G.hom
  exact ⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩
end GlobalTheory
