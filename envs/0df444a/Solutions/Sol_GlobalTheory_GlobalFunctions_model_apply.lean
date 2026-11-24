-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.model_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:32:57.863434+00:00
-- url     : https://prove2.me/submissions/3de98c7d-2b4a-428c-86e3-c3cae2e0c7dd

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
theorem _root_.solution {R₀ R B₀ B C₀ C : Type} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : R ⊗[R₀] B₀) :
    u (β y) = δ (u₀.baseChange R y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have h1 : ∀ {M : Type} [AddCommGroup M] [Module R₀ M] (m : M),
        (c ⊗ₜ[R₀] m : R ⊗[R₀] M) = c • (1 ⊗ₜ m) := by
      intro M _ _ m
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [LinearMap.baseChange_tmul, h1 b, h1 (u₀ b), map_smul, map_smul, map_smul, h]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.GlobalFunctions
