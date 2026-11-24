-- Prove2me | solution 1 for GlobalTheory.FlatFibreInjective.one_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:47.46308+00:00
-- url     : https://prove2.me/submissions/a0bb7436-e990-44b2-b7ca-5f5e60139dea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct
namespace GlobalTheory.FlatFibreInjective
theorem _root_.solution {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by
  obtain ⟨g, hg⟩ := (φ.baseChange k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hφ)
  have key : ∀ z : M ⊗[R₀] C₀,
      TensorProduct.leftComm R₀ M k C₀ ((g.restrictScalars R₀).lTensor M
        ((TensorProduct.mk R₀ k C₁ 1).lTensor M (φ.lTensor M z))) = (1 : k) ⊗ₜ[R₀] z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      have := LinearMap.congr_fun hg ((1 : k) ⊗ₜ[R₀] c)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at this
      simp [this]
    | add a b ha hb => simp only [map_add, ha, hb, tmul_add]
  rw [← key, hy]
  simp
end GlobalTheory.FlatFibreInjective
