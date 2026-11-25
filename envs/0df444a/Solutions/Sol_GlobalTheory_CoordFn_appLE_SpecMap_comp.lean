-- Prove2me | solution 1 for GlobalTheory.CoordFn.appLE_SpecMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:13.559282+00:00
-- url     : https://prove2.me/submissions/fd11c705-0079-4dfd-b4f4-d605e067a4b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsIsoAppLEOfOpensRange

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
theorem _root_.solution {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : B ⟶ A)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (p : Spec A ⟶ Y) (hp : p = Spec.map g ≫ f)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) :
    p.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso A).hom = f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom ≫ g := by
  subst hp
  have e1 : (Spec.map g).appTop = (Spec.map g).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.app_eq_appLE (Spec.map g)
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map g) f U ⊤ ⊤ h le_top
  rw [← Scheme.ΓSpecIso_naturality, e1, ← Category.assoc, e2]
end GlobalTheory.CoordFn
