-- Prove2me | solution 1 for GlobalTheory.CoordToExt.prod_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:10.800367+00:00
-- url     : https://prove2.me/submissions/d3747a65-5f25-4bfa-903e-fd28696ef6b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
namespace GlobalTheory.CoordToExt
theorem _root_.solution {S : Scheme.{0}} {B T : Over S} [GrpObj B] (x : Fin 2 → (T ⟶ B)) {U : Type} [CommGroup U]
    (F : (T ⟶ B) → U) :
    ∏ J : ULift.{0} (Finset (Fin 2)), F (psum B x J.down) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      F 1 * (F (x 0))⁻¹ * (F (x 1))⁻¹ * F (x 0 * x 1) := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun J => F (psum B x J) ^ ((-1 : ℤ) ^ (2 - J.card))) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B x ∅ = 1 := rfl
  have p₁ : psum B x {0} = x 0 := _root_.mul_one (x 0)
  have p₂ : psum B x {1} = x 1 := _root_.mul_one (x 1)
  have p₃ : psum B x {0, 1} = x 0 * x 1 := congrArg (x 0 * ·) (_root_.mul_one (x 1))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one, _root_.mul_assoc]
end GlobalTheory.CoordToExt
