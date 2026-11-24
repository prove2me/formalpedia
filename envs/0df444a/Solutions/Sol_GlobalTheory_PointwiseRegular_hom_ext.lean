-- Prove2me | solution 1 for GlobalTheory.PointwiseRegular.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:07.918585+00:00
-- url     : https://prove2.me/submissions/ff61389f-6435-47af-9861-2998694757a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
import Theorems.Thm_GlobalTheory_ComplexPoints_hom_ext_of_points
import Theorems.Thm_GlobalTheory_ComplexPoints_opens_le_of_complexPoints
import Theorems.Thm_GlobalTheory_top_le_preimage_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.PointwiseRegular
namespace GlobalTheory.PointwiseRegular
theorem _root_.solution {X Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced Y] {f g : Y ⟶ X}
    (h : ∀ y : Sp ℂ ⟶ Y, y ≫ p = 𝟙 _ → y ≫ f = y ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨_, ⟨D, hD, rfl⟩, hz, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  have hle : f ⁻¹ᵁ D ≤ g ⁻¹ᵁ D := ComplexPoints.opens_le_of_complexPoints p _ _ fun y hy hyD => by
    rw [← top_le_preimage_comp] at hyD ⊢
    rwa [← h y hy]
  refine ⟨f ⁻¹ᵁ D, hz, ?_⟩
  have : IsAffine (Scheme.Opens.toScheme (X := X) D) := hD
  have key : f.resLE D (f ⁻¹ᵁ D) le_rfl = g.resLE D (f ⁻¹ᵁ D) hle := by
    refine ComplexPoints.hom_ext_of_points ((f ⁻¹ᵁ D).ι ≫ p) (terminal.from _) (terminal.hom_ext _ _) fun x hx => ?_
    rw [← cancel_mono (Scheme.Opens.ι (X := X) D), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, ← Category.assoc]
    exact h _ (by rw [Category.assoc]; exact hx)
  rw [← Scheme.Hom.resLE_comp_ι f le_rfl, key, Scheme.Hom.resLE_comp_ι]
end GlobalTheory.PointwiseRegular
