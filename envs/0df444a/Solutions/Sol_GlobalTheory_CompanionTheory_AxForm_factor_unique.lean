-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.factor_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:55.888839+00:00
-- url     : https://prove2.me/submissions/575fafe4-a0fd-4e2a-a249-5e6c0326a2a5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] {t t' : Sec s U.1 →+* C}
    (h : spMap t ≫ affPt s U = spMap t' ≫ affPt s U) : t = t' := by
  haveI : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec
  have := Spec.map_injective ((cancel_mono (affPt s U)).1 h)
  exact congrArg CommRingCat.Hom.hom this
end GlobalTheory.CompanionTheory.AxForm
