-- Prove2me | solution 1 for GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:39.520372+00:00
-- url     : https://prove2.me/submissions/3120222b-fa81-4e7f-a26c-d5daaee4d1d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (_hAB : Function.Injective (algebraMap A B))
    (hfrac : ∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    IsDomain (TensorProduct A B R) ∧
      Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by

  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
    have hcomp : ∀ r : R, (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) r =
        (LinearMap.rTensor R (Algebra.linearMap A B)) ((TensorProduct.lid A R).symm r) := by
      intro r
      simp [Algebra.TensorProduct.includeRight_apply]
    intro r r' h
    rw [hcomp, hcomp] at h
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := R) (Algebra.linearMap A B) _hAB h
    exact (TensorProduct.lid A R).symm.injective h1

  have hmove : ∀ (a : A) (r : R), (algebraMap A B a) ⊗ₜ[A] r = (1 : B) ⊗ₜ[A] (algebraMap A R a * r) := by
    intro a r
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

  have hmulInj : ∀ c : B, c ≠ 0 → ∀ x : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * x = 0 → x = 0 := by
    intro c hc x hx
    have heq : ∀ y : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * y =
        (LinearMap.rTensor R (LinearMap.mulLeft A c)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b r => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => rw [mul_add, map_add, hy, hz]
    have hinjc : Function.Injective (LinearMap.mulLeft A c) := by
      intro u v huv
      exact mul_left_cancel₀ hc huv
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hinjc
    apply this
    rw [← heq, hx, map_zero]

  have hden : ∀ x : TensorProduct A B R, ∃ s : A, algebraMap A B s ≠ 0 ∧
      ∃ r : R, (algebraMap A B s ⊗ₜ[A] (1 : R)) * x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul b r =>
      obtain ⟨a, s, hs, hsb⟩ := hfrac b
      refine ⟨s, hs, algebraMap A R a * r, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, hsb, one_mul, hmove]
    | add x y hx hy =>
      obtain ⟨s, hs, r, hr⟩ := hx
      obtain ⟨s', hs', r', hr'⟩ := hy
      refine ⟨s * s', by rw [map_mul]; exact mul_ne_zero hs hs',
        algebraMap A R s' * r + algebraMap A R s * r', ?_⟩
      have e1 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s' ⊗ₜ[A] (1 : R)) * (algebraMap A B s ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, mul_comm]
      have e2 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s ⊗ₜ[A] (1 : R)) * (algebraMap A B s' ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      rw [mul_add]
      conv_lhs => arg 1; rw [e1, mul_assoc, hr]
      conv_lhs => arg 2; rw [e2, mul_assoc, hr']
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
        hmove, hmove, one_mul, one_mul, ← TensorProduct.tmul_add]

  haveI : Nontrivial (TensorProduct A B R) := by
    refine ⟨⟨Algebra.TensorProduct.includeRight (1 : R), Algebra.TensorProduct.includeRight (0 : R), ?_⟩⟩
    intro h
    exact one_ne_zero (hinc h)
  haveI : NoZeroDivisors (TensorProduct A B R) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨s, hs, r, hr⟩ := hden x
    obtain ⟨s', hs', r', hr'⟩ := hden y
    have hprod : (1 : B) ⊗ₜ[A] (r * r') = 0 := by
      have : ((algebraMap A B s ⊗ₜ[A] (1 : R)) * x) * ((algebraMap A B s' ⊗ₜ[A] (1 : R)) * y) = 0 := by
        rw [mul_mul_mul_comm, hxy, mul_zero]
      rw [hr, hr', Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
      exact this
    have hrr : r * r' = 0 := by
      apply hinc
      rw [map_zero, Algebra.TensorProduct.includeRight_apply]
      exact hprod
    rcases mul_eq_zero.mp hrr with h0 | h0
    · left
      apply hmulInj _ hs
      rw [hr, h0, TensorProduct.tmul_zero]
    · right
      apply hmulInj _ hs'
      rw [hr', h0, TensorProduct.tmul_zero]
  exact ⟨NoZeroDivisors.to_isDomain _, hinc⟩
end GlobalTheory
