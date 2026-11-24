-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.factor_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:07.241871+00:00
-- url     : https://prove2.me/submissions/f56c5a9e-37f9-4a34-bf85-72fb23e37da0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
theorem _root_.solution (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] (t : Sec s U.1 →+* C)
    (ρ : R →+* C) (h : (spMap t ≫ affPt s U) ≫ s = spMap ρ) : t.comp (algebraMap R (Sec s U.1)) = ρ := by
  have e : spMap (t.comp (algebraMap R (Sec s U.1))) = spMap ρ := by
    rw [spMap_comp, ← h, Category.assoc, affPt_w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
end GlobalTheory.CompanionTheory.AxForm
