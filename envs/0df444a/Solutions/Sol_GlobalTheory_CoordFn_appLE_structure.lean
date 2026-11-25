-- Prove2me | solution 1 for GlobalTheory.CoordFn.appLE_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:17.023802+00:00
-- url     : https://prove2.me/submissions/a77a6583-a001-4a3f-9a98-a55cd6552bfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsIsoAppLEOfOpensRange
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.CoordFn
namespace GlobalTheory.CoordFn
theorem _root_.solution {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : A ⟶ B)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (t : Y ⟶ Spec A) (ht : f ≫ t = Spec.map g) :
    (Scheme.ΓSpecIso A).inv ≫ t.appLE ⊤ U le_top ≫ f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = g := by
  have e2 := Scheme.Hom.appLE_comp_appLE f t ⊤ U ⊤ le_top h
  have e1 : ∀ (q : Spec B ⟶ Spec A) (hq : ⊤ ≤ q ⁻¹ᵁ ⊤), q = Spec.map g →
      q.appLE ⊤ ⊤ hq = (Spec.map g).appTop := by
    rintro _ _ rfl
    exact (Scheme.Hom.app_eq_appLE (Spec.map g)).symm
  rw [← Category.assoc (t.appLE ⊤ U le_top), e2, e1 _ _ ht, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]
end GlobalTheory.CoordFn
