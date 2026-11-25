-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.unit_eq_one_of_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:48.426802+00:00
-- url     : https://prove2.me/submissions/c5f1107b-5fe4-4000-a886-d1e7ff04278e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_unit_on_product_eq_one


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
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] (e : Spec (.of K) ⟶ X) (he : e ≫ f = 𝟙 _)
    (a₁ a₂ : X ⟶ pullback f f) (h₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁' : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂' : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (u₁ : a₁.appTop.hom u = 1) (u₂ : a₂.appTop.hom u = 1) :
    u = 1 := by
  first
  | exact @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | (apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one ..)
end GlobalTheory.UnitRigidity
