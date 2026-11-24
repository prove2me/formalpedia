-- Prove2me | solution 1 for GlobalTheory.JacGen.valT_specMap_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:03.701939+00:00
-- url     : https://prove2.me/submissions/0f182fc0-2d8c-42a2-b6ec-33937437659e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}
namespace GlobalTheory.JacGen
theorem _root_.solution {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) {T : Type} [CommRing T]
    (φ : X.presheaf.stalk y ⟶ .of T) (f : Γ(X, U)) :
    KeyKa.valT (T := T) (Spec.map φ ≫ X.fromSpecStalk y) U f = φ.hom ((X.presheaf.germ U y hy).hom f) := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ X.fromSpecStalk y) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  refine (dif_pos ht').trans ?_
  have h1 : (X.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (X.presheaf.stalk y)).hom =
      X.presheaf.germ U y hy := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE (le_top : X.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  have h2 : (Spec.map φ ≫ X.fromSpecStalk y).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso (.of T)).hom =
      X.presheaf.germ U y hy ≫ φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, ← h1, Category.assoc, Category.assoc,
      ← Scheme.ΓSpecIso_naturality]
    congr 2
  exact congrArg (fun q => q.hom f) h2
end GlobalTheory.JacGen
