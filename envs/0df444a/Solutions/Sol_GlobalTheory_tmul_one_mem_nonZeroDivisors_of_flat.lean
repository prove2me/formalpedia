-- Prove2me | solution 1 for GlobalTheory.tmul_one_mem_nonZeroDivisors_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:59.134802+00:00
-- url     : https://prove2.me/submissions/883e0f7e-c650-49e1-bfd9-d0a072a98588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsMaximalTensorProductOfIsLocalHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])
end GlobalTheory
