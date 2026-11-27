-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.appTop_SpecMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:11.407376+00:00
-- url     : https://prove2.me/submissions/039aa14f-36e3-41c4-a9bf-6931b47c69b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
open scoped TensorProduct
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {R S : CommRingCat.{0}} (φ : R ⟶ S) {X : Scheme.{0}} (g : Spec R ⟶ X)
    (u : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom ((Spec.map φ ≫ g).appTop.hom u) =
      φ.hom ((Scheme.ΓSpecIso R).hom.hom (g.appTop.hom u)) := by
  rw [Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl
end GlobalTheory.UnitRigidity
