-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:01.976553+00:00
-- url     : https://prove2.me/submissions/001a593b-d920-4fae-b1f0-6308383d1524

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSectionsAffineFlat
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s →
    ∀ U : X.affineOpens, Module.Flat R (Sec s U.1) := by
  intro R _ X s hs U
  haveI : Smooth s := hs
  have hfl : Flat s := inferInstance
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  have h1 := HasRingHomProperty.appLE @Flat s hfl ⟨⊤, hT⟩ U le_top
  have h2 : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h3 := RingHom.Flat.comp h2 h1
  exact h3
end GlobalTheory.CompanionTheory.Axis
