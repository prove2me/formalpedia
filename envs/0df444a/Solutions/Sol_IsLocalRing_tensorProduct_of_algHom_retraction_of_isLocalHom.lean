-- Prove2me | solution 1 for IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/18e7a404-892e-5f4b-b06d-af602cd0483d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom

open scoped TensorProduct
open IsLocalRing

theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Finite R A]
    (ε : A →ₐ[R] R)
    (O : Type*) [CommRing O] [Algebra R O] [IsLocalRing O] [IsLocalHom (algebraMap R O)] :
    IsLocalRing (O ⊗[R] A) := by
  classical

  let φ : O ⊗[R] A →ₐ[O] O := Algebra.TensorProduct.lift (AlgHom.id O O)
      ((Algebra.ofId R O).comp ε) (fun _ _ => Commute.all _ _)
  haveI : Nontrivial (O ⊗[R] A) := φ.toRingHom.domain_nontrivial

  have h1 : ∀ N : Ideal (O ⊗[R] A), N.IsMaximal →
      (maximalIdeal O).map (algebraMap O (O ⊗[R] A)) ≤ N := by
    intro N hN
    rw [Ideal.map_le_iff_le_comap]
    haveI := hN
    exact (eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) N)).symm.le

  have hεloc : ∀ a : A, ε a = 0 → a ∈ maximalIdeal A := by
    intro a ha hu
    exact not_isUnit_zero (ha ▸ hu.map ε)
  let I : Ideal A := (maximalIdeal R).map (algebraMap R A)
  haveI : IsArtinianRing (A ⧸ I) :=
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    haveI : Module.Finite (R ⧸ maximalIdeal R) (A ⧸ I) :=
      Module.Finite.of_restrictScalars_finite R _ _
    IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (A ⧸ I)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

  have hRO : (algebraMap R (O ⊗[R] A)) = (algebraMap O (O ⊗[R] A)).comp (algebraMap R O) :=
    IsScalarTower.algebraMap_eq R O (O ⊗[R] A)
  have h2 : ∀ a : A, ε a = 0 → (1 : O) ⊗ₜ[R] a ∈ (⊥ : Ideal (O ⊗[R] A)).jacobson := by
    intro a ha
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro N ⟨-, hN⟩
    have han : a ^ n ∈ I := hn (Ideal.pow_mem_pow (hεloc a ha) n)
    have hmem : (Algebra.TensorProduct.includeRight : A →ₐ[R] O ⊗[R] A) (a ^ n) ∈
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] O ⊗[R] A) :=
      Ideal.mem_map_of_mem _ han
    have hle : I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] O ⊗[R] A) ≤
        (maximalIdeal O).map (algebraMap O (O ⊗[R] A)) := by
      rw [← Ideal.map_coe Algebra.TensorProduct.includeRight, Ideal.map_map,
        AlgHom.comp_algebraMap, hRO, ← Ideal.map_map]
      exact Ideal.map_mono (map_maximalIdeal_le _)
    have : ((1 : O) ⊗ₜ[R] a) ^ n ∈ N := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      exact h1 N hN (hle hmem)
    exact hN.isPrime.mem_of_pow_mem n this
  have h3 : ∀ o ∈ maximalIdeal O,
      algebraMap O (O ⊗[R] A) o ∈ (⊥ : Ideal (O ⊗[R] A)).jacobson := by
    intro o ho
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro N ⟨-, hN⟩
    exact h1 N hN (Ideal.mem_map_of_mem _ ho)

  have e1 : ∀ o : O, algebraMap O (O ⊗[R] A) o = o ⊗ₜ[R] 1 := fun o => by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h4 : ∀ x : O ⊗[R] A, ∃ o : O,
      x - algebraMap O (O ⊗[R] A) o ∈ (⊥ : Ideal (O ⊗[R] A)).jacobson := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o a =>
      refine ⟨ε a • o, ?_⟩
      have : o ⊗ₜ[R] a - algebraMap O (O ⊗[R] A) (ε a • o) =
          (o ⊗ₜ[R] (1 : A)) * ((1 : O) ⊗ₜ[R] (a - ε a • (1 : A))) := by
        rw [e1, TensorProduct.smul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
          TensorProduct.tmul_sub]
      rw [this]
      exact Ideal.mul_mem_left _ _ (h2 _ (by simp))
    | add x y hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      rw [map_add, ← sub_add_sub_comm]
      exact add_mem h₁ h₂

  have key : ∀ (c j : O ⊗[R] A), IsUnit c → j ∈ (⊥ : Ideal (O ⊗[R] A)).jacobson →
      IsUnit (c + j) := by
    intro c j hc hj
    obtain ⟨w, hw⟩ := hc.exists_right_inv
    have hu := Ideal.mem_jacobson_bot.mp hj w
    have : c + j = c * (j * w + 1) := by
      calc c + j = c + j * (c * w) := by rw [hw, mul_one]
        _ = c * (j * w + 1) := by ring
    rw [this]
    exact hc.mul hu
  refine of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨o, hj⟩ := h4 x
  rcases isUnit_or_isUnit_one_sub_self o with ho | ho
  · left
    have : x = algebraMap O (O ⊗[R] A) o + (x - algebraMap O (O ⊗[R] A) o) := by ring
    rw [this]
    exact key _ _ (ho.map _) hj
  · right
    have : 1 - x = algebraMap O (O ⊗[R] A) (1 - o) + -(x - algebraMap O (O ⊗[R] A) o) := by
      rw [map_sub, map_one]; ring
    rw [this]
    exact key _ _ (ho.map _) (neg_mem hj)

end S_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom
end P2MW
export P2MW.S_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom (solution)
