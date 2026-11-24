-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.baseChange_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:32:46.466466+00:00
-- url     : https://prove2.me/submissions/17d09b09-3ba5-451a-9f39-a38a965d2488

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution {R₀ R k B₀ B C₀ C : Type} [CommRing R₀] [CommRing R] [CommRing k]
    [Algebra R₀ R] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k]
    [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : k ⊗[R₀] B₀) :
    u.baseChange k (β.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y)) =
    δ.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k C₀).symm (u₀.baseChange k y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b => simp [h]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.GlobalFunctions
