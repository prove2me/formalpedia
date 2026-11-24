-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.eq_zero_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:28.380389+00:00
-- url     : https://prove2.me/submissions/d5d9a714-ffb8-4fa2-8697-87382e019875

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_baseChange_model
import Theorems.Thm_GlobalTheory_GlobalFunctions_model_apply

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
theorem _root_.solution (hI : FibreInjective) (hD : SmoothDescent) {R B C : Type} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C]
    (f g : B →ₐ[R] C) (r : B →ₐ[R] R)
    (hk : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B),
      f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x →
      r.toLinearMap.baseChange k x = 0 → x = 0)
    (b : B) (hb : f b = g b) (hr : r b = 0) : b = 0 := by
  obtain ⟨R₀, B₀, C₀, _, _, _, _, _, _, _, f₀, g₀, r₀, β, δ, _, _, h⟩ := hD R B C f g r
  let ρ : R ⊗[R₀] R₀ ≃ₗ[R] R := AlgebraTensorModule.rid R₀ R R
  have hf : ∀ b, f.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ f₀.toLinearMap b) := fun b ↦ (h b).1
  have hg : ∀ b, g.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ g₀.toLinearMap b) := fun b ↦ (h b).2.1
  have hr' : ∀ b, r.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      ρ (1 ⊗ₜ r₀.toLinearMap b) := fun b ↦ (h b).2.2.trans (by
        simp [ρ, Algebra.algebraMap_eq_smul_one])
  let φ : B₀ →ₗ[R₀] C₀ × R₀ := (f₀.toLinearMap - g₀.toLinearMap).prod r₀.toLinearMap
  have : Module.Flat R₀ (C₀ × R₀) := flat_prod
  have hφ : Function.Injective (φ.baseChange R) := by
    refine hI R₀ R B₀ (C₀ × R₀) φ fun k _ _ _ _ ↦ ?_
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : (f₀.toLinearMap - g₀.toLinearMap).baseChange k y = 0 := by
      have : f₀.toLinearMap - g₀.toLinearMap = (LinearMap.fst R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    have h2 : r₀.toLinearMap.baseChange k y = 0 := by
      have : r₀.toLinearMap = (LinearMap.snd R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, sub_eq_zero] at h1
    have h3 := hk k (β.toLinearEquiv.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y))
      (by rw [baseChange_model _ _ _ _ hf, baseChange_model _ _ _ _ hg, h1])
      (by rw [baseChange_model _ _ _ _ hr', h2, map_zero, map_zero])
    have h4 : (β.toLinearEquiv.baseChange R k _ _)
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y) = 0 := h3
    simpa using h4
  obtain ⟨y, rfl⟩ := β.surjective b
  have h1 : f₀.toLinearMap.baseChange R y = g₀.toLinearMap.baseChange R y := by
    apply δ.toLinearEquiv.injective
    rw [← model_apply _ _ _ _ hf, ← model_apply _ _ _ _ hg]
    exact hb
  have h2 : r₀.toLinearMap.baseChange R y = 0 := by
    apply ρ.injective
    rw [← model_apply _ _ _ _ hr', map_zero]
    exact hr
  have h3 : φ = LinearMap.inl R₀ C₀ R₀ ∘ₗ (f₀.toLinearMap - g₀.toLinearMap) +
      LinearMap.inr R₀ C₀ R₀ ∘ₗ r₀.toLinearMap := by
    ext x <;> simp [φ]
  have : y = 0 := by
    apply hφ
    rw [map_zero, h3, LinearMap.baseChange_add, LinearMap.add_apply, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, h2,
      LinearMap.baseChange_sub, LinearMap.sub_apply, h1, sub_self, map_zero, map_zero, add_zero]
  rw [this, map_zero]
end GlobalTheory.GlobalFunctions
