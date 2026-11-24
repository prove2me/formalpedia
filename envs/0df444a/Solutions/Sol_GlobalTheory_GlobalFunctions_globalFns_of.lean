-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.globalFns_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:18.298452+00:00
-- url     : https://prove2.me/submissions/0de02a47-f6ec-4a10-9385-2f34ae2d5685

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_isIso_app
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app


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
theorem _root_.solution : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀] [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁), (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k], Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R)) → (∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b)) → GlobalFnsSt := by
  intro hG hI hD S A _ hA
  have := hA.smooth
  have := hA.proper
  have := hG _ _ A.hom hA.smooth hA.geomConnected
  have : IsIso A.hom.appTop := isIso_app hI hD A.hom ⊤
  exact ConcreteCategory.bijective_of_isIso A.hom.appTop
end GlobalTheory.GlobalFunctions
