-- Prove2me | solution 1 for GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:37.734189+00:00
-- url     : https://prove2.me/submissions/8861bda2-ce2c-4827-843b-a05badfc6d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  intro F _ B _ _ V V' _ _ _ _ _ m hm y hy
  have hinj : Function.Injective m.flip :=
    (injective_iff_map_eq_zero m.flip).2 fun z h =>
      hm z fun x => by simpa using LinearMap.congr_fun h x
  have hsurj : Function.Surjective m := LinearMap.flip_injective_iff₂.1 hinj
  let b := Module.finBasis F V'
  have key : ∀ z : V' ⊗[F] B,
      z = ∑ j, b j ⊗ₜ (TensorProduct.lid F B (LinearMap.rTensor B (b.coord j) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add z₁ z₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  rw [key y]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨v, hv⟩ := hsurj (b.coord j)
  rw [← hv, hy v, TensorProduct.tmul_zero]
end GlobalTheory
