-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.translate_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:48.436199+00:00
-- url     : https://prove2.me/submissions/8cfc28a5-035a-46bc-b7ce-9ed78b4fd4df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] {f : R →+* R'}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (z : 𝟙_ (Over (Sp R)) ⟶ G) (z' : 𝟙_ (Over (Sp R')) ⟶ G') (hz : z'.left ≫ φ = spMap f ≫ z.left)
    (v : epsR R ⟶ G) (v' : epsR R' ⟶ G') (hv : v'.left ≫ φ = spMap F ≫ v.left) :
    ((toUnit (epsR R') ≫ z') * v').left ≫ φ = spMap F ≫ ((toUnit (epsR R) ≫ z) * v).left := by
  have hd : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    have : F.comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := RingHom.ext h₁
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  let D : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap F) hd
  have e : (D ≫ toUnit (epsR R) ≫ z).left = (toUnit (epsR R') ≫ z').left ≫ φ := by
    show spMap F ≫ (epsR R).hom ≫ z.left = ((epsR R').hom ≫ z'.left) ≫ φ
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ z.left) hd).trans ((Category.assoc _ _ _).trans
      ((congrArg ((epsR R').hom ≫ ·) hz.symm).trans (Category.assoc _ _ _).symm)))
  rw [← h.2 (epsR R') _ _ (D ≫ toUnit (epsR R) ≫ z) (D ≫ v) e hv.symm, ← MonObj.comp_mul]
  rfl
end GlobalTheory.KeyKa.EtBaseChange
