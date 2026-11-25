-- Prove2me | solution 1 for GroundTheory.GroupCoh.injective_of_lTensor_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:41.304642+00:00
-- url     : https://prove2.me/submissions/f7a89747-263a-4ac1-8170-acab8b164589

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable {A B : Rep.{u} k G}
variable {W P₁ P₂ Q₁ Q₂ : Type u} [AddCommGroup W] [Module k W] [Module.Flat k W]
  [AddCommGroup P₁] [Module k P₁] [AddCommGroup P₂] [Module k P₂]
  [AddCommGroup Q₁] [Module k Q₁] [AddCommGroup Q₂] [Module k Q₂]
namespace GroundTheory.GroupCoh
theorem _root_.solution (φ : P₁ →ₗ[k] P₂) (ψ : Q₁ →ₗ[k] Q₂)
    (hψ : Function.Injective ψ) (e₁ : P₁ ≃ₗ[k] TensorProduct k W Q₁)
    (e₂ : P₂ ≃ₗ[k] TensorProduct k W Q₂) (h : ∀ x, e₂ (φ x) = LinearMap.lTensor W ψ (e₁ x)) :
    Function.Injective φ := by
  intro x y hxy
  apply e₁.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  rw [← h, ← h, hxy]
end GroundTheory.GroupCoh
