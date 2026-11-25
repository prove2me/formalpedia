-- Prove2me | solution 1 for GlobalTheory.LBLimit.exists_appLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:44.884864+00:00
-- url     : https://prove2.me/submissions/8598835c-61fa-4255-a9af-962c8d122e28

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
set_option backward.isDefEq.respectTransparency false
include hc
namespace GlobalTheory.LBLimit
theorem _root_.solution {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isLimit _ _
    (isLimitOpensCone D _ hc i U) ((π i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have h := (congrArg (π i ⁻¹ᵁ U).topIso.hom hj.symm).trans (Iso.inv_hom_id_apply _ s)
  have e : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), (f.appLE U V e).hom (U.topIso.hom t) =
        V.topIso.hom ((f.resLE U V e).appTop t) := by
    intro X Y f U V e t
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  exact (e _ _ _ _ t).trans h
end GlobalTheory.LBLimit
