-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:04.982564+00:00
-- url     : https://prove2.me/submissions/ce65d8c7-f55e-48ec-ba56-f018f797c626

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
theorem _root_.solution (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] (y : Sp C ⟶ X)
    (hy : ∀ z, y z ∈ U.1) : ∃ t : Sec s U.1 →+* C, spMap t ≫ affPt s U = y := by
  haveI : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec
  have hr : Set.range y ⊆ Set.range (affPt s U) := by
    rintro _ ⟨z, rfl⟩
    have := U.2.range_fromSpec
    change _ ∈ Set.range U.2.fromSpec
    rw [this]
    exact hy z
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (affPt s U) y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift (affPt s U) y hr)).hom =
      IsOpenImmersion.lift (affPt s U) y hr := Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _
end GlobalTheory.CompanionTheory.AxForm
