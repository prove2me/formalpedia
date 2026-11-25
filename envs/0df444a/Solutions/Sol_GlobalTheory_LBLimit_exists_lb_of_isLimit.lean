-- Prove2me | solution 1 for GlobalTheory.LBLimit.exists_lb_of_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:45:04.196967+00:00
-- url     : https://prove2.me/submissions/34cb659c-7c5e-4df0-8396-f8dae54385cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRefinementOfIsLimit
import Theorems.Thm_GlobalTheory_LBLimit_lbIso_of_refinement
import Theorems.Thm_GlobalTheory_LBLimit_exists_refinement_of_isLimit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.LBLimit
variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, QuasiSeparatedSpace (D.obj i)]
include hc
namespace GlobalTheory.LBLimit
theorem _root_.solution [∀ i, CompactSpace (D.obj i)] (L : LB X) (hL : L.IsLB) :
    ∃ (j : I) (M : LB (D.obj j)), M.IsLB ∧ LBIso L (M.pull (π j)) ∧
      ∀ (Y : Scheme.{0}) (r : X ⟶ Y) (q : Y ⟶ D.obj j), r ≫ q = π j → LBIso L ((M.pull q).pull r) := by
  obtain ⟨j, M, e, hM, he, hg⟩ := exists_refinement_of_isLimit D π w hc L hL
  refine ⟨j, M, hM, lbIso_of_refinement L _ hL (fun J => e (J PUnit.unit))
    (fun J y hy => he _ (mem_pull.1 hy)) fun J J' y hy hy' => ?_, fun Y r q hr => ?_⟩
  · refine (gm_pull_g M (π j) (𝟙 X) y J J' hy hy').trans ?_
    rw [Category.id_comp]
    exact hg _ _ y (mem_pull.1 hy) (mem_pull.1 hy')
  · have m : ∀ (J : ((M.pull q).pull r).ι) (y : X), y ∈ ((M.pull q).pull r).U J →
        π j y ∈ M.U (J PUnit.unit PUnit.unit) := fun J y hy => by
      rw [← hr]
      exact (mem_pull (L := M) (F := q) (x := r y)).1 (mem_pull.1 hy)
    refine lbIso_of_refinement L _ hL (fun J => e (J PUnit.unit PUnit.unit))
      (fun J y hy => he _ (m J y hy)) fun J J' y hy hy' => ?_
    refine (gm_pull_g (M.pull q) r (𝟙 X) y J J' hy hy').trans ?_
    rw [Category.id_comp]
    refine (gm_pull_g M q r y _ _ (mem_pull.1 hy) (mem_pull.1 hy')).trans ?_
    rw [hr]
    exact hg _ _ y (m J y hy) (m J' y hy')
end GlobalTheory.LBLimit
