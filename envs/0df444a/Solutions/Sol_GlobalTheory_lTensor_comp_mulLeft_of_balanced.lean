-- Prove2me | solution 1 for GlobalTheory.lTensor_comp_mulLeft_of_balanced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:59.387553+00:00
-- url     : https://prove2.me/submissions/45828626-e41a-42d7-8c78-df0a70a4709b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]
namespace GlobalTheory
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module O N]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (α : H →ₗ[O] N) (h : H) :
    LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) Θ = h • LinearMap.lTensor H α Θ := by
  have h1 : ∀ t : H ⊗[O] H, LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) t
      = LinearMap.lTensor H α (((1 : H) ⊗ₜ[O] h) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h2 : ∀ t : H ⊗[O] H, h • LinearMap.lTensor H α t
      = LinearMap.lTensor H α ((h ⊗ₜ[O] (1 : H)) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]
  rw [h1, h2, hΘ]
end GlobalTheory
