-- Prove2me | solution 1 for GlobalTheory.algHom_ext_of_sub_mem_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:14.275929+00:00
-- url     : https://prove2.me/submissions/ce5a08d7-2b3d-4d2f-b99c-b42beae6560c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {f g : A →ₐ[R] B} (h : ∀ a, f a - g a ∈ (⊥ : Ideal B).jacobson) : f = g := by
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).1
    inferInstance
  let φ : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift f g fun _ _ ↦ .all _ _
  have key : ∀ x : A ⊗[R] A, f (Algebra.TensorProduct.lmul' R x) - φ x ∈
      (⊥ : Ideal B).jacobson := by
    intro x
    induction x with
    | zero => simp
    | tmul a b =>
      have : f (Algebra.TensorProduct.lmul' R (a ⊗ₜ b)) - φ (a ⊗ₜ b) = f a * (f b - g b) := by
        simp [φ, mul_sub]
      rw [this]
      exact Ideal.mul_mem_left _ _ (h b)
    | add x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
  have hu : IsUnit (φ t) := by
    have h1 := key t
    rw [ht1, map_one] at h1
    have := Ideal.mem_jacobson_bot.1 h1 (-1)
    simpa using this
  ext a
  have := congr(φ $(ht a))
  simp only [map_mul, map_sub, map_zero, φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    mul_one] at this
  exact (sub_eq_zero.1 ((hu.mul_left_eq_zero).1 this)).symm
end GlobalTheory
