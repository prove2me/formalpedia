-- Prove2me | solution 1 for GlobalTheory.BiextSym.biextension_first_law_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:08.10637+00:00
-- url     : https://prove2.me/submissions/fc53deeb-b9d5-477d-afcd-b1bfd717a648

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.BiextSym
theorem _root_.solution {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]
end GlobalTheory.BiextSym
