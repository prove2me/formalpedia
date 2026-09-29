-- Prove2me | solution 1 for Ideal.minimalPrimes_tensorProduct_fractionRing_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9794868c-b196-55d1-a23e-45b2a5ca7c06

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary

set_option autoImplicit false
open scoped TensorProduct

namespace DICT42

open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem parts12 {S B F : Type} [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.IsIntegral S B] [CommRing F] [Algebra S F] [IsFractionRing S F]
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, Ideal.comap (algebraMap S B) 𝔭 = ⊥) :
    (∀ 𝔓 : Ideal (F ⊗[S] B), 𝔓.IsPrime →
        Ideal.comap (includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, ∃! 𝔓 : Ideal (F ⊗[S] B),
        𝔓.IsPrime ∧ Ideal.comap (includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 = 𝔭) := by
  set M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors S) with hM
  haveI : IsLocalization M (F ⊗[S] B) :=
    IsLocalization.tensorRight (R := S) (S := B) F (nonZeroDivisors S)
  have hcomap : ∀ 𝔓 : Ideal (F ⊗[S] B),
      Ideal.comap (includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 = 𝔓.under B := fun 𝔓 => rfl

  have hdisj : ∀ 𝔮 : Ideal B, Disjoint (M : Set B) 𝔮 ↔ Ideal.comap (algebraMap S B) 𝔮 = ⊥ := by
    intro 𝔮
    constructor
    · intro hd
      rw [eq_bot_iff]
      intro s hs
      rw [Ideal.mem_comap] at hs
      rw [Ideal.mem_bot]
      by_contra hs0
      have hsM : algebraMap S B s ∈ M :=
        Algebra.mem_algebraMapSubmonoid_of_mem (⟨s, mem_nonZeroDivisors_of_ne_zero hs0⟩ : nonZeroDivisors S)
      exact Set.disjoint_left.mp hd hsM hs
    · intro h
      refine Set.disjoint_left.mpr ?_
      rintro b ⟨s, hs, rfl⟩ hmem
      have h' : s ∈ Ideal.comap (algebraMap S B) 𝔮 := hmem
      rw [h, Ideal.mem_bot] at h'
      exact nonZeroDivisors.ne_zero hs h'

  have hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → Ideal.comap (algebraMap S B) 𝔮 = ⊥ →
      𝔮 ∈ (⊥ : Ideal B).minimalPrimes := by
    intro 𝔮 h𝔮 h0
    refine ⟨⟨h𝔮, bot_le⟩, ?_⟩
    rintro 𝔮' ⟨h𝔮', -⟩ hle
    by_contra hne
    have hlt : 𝔮' < 𝔮 := lt_of_le_of_ne hle (fun h => hne (h ▸ le_rfl))
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := S) hlt
    rw [h0] at hlt'
    exact not_lt_bot hlt'
  constructor
  · intro 𝔓 h𝔓
    obtain ⟨hprime, hd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint M (F ⊗[S] B) 𝔓).mp h𝔓
    rw [hcomap]
    exact hmin _ hprime ((hdisj _).mp hd)
  · intro 𝔭 h𝔭
    have hprime : 𝔭.IsPrime := h𝔭.1.1
    have hd : Disjoint (M : Set B) 𝔭 := (hdisj 𝔭).mpr (hdom 𝔭 h𝔭)
    refine ⟨Ideal.map (algebraMap B (F ⊗[S] B)) 𝔭,
      ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ 𝔭 hprime hd, ?_⟩, ?_⟩
    · rw [hcomap]
      exact IsLocalization.under_map_of_isPrime_disjoint M _ hprime hd
    · rintro 𝔓' ⟨-, hc⟩
      rw [hcomap] at hc
      rw [← hc]
      exact (IsLocalization.map_under M (F ⊗[S] B) 𝔓').symm

theorem part3 {S B F : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing F] [Algebra S F]
    (e : B ≃ₐ[S] B) :
    ∃ ee : F ⊗[S] B ≃ₐ[F] F ⊗[S] B, ∀ b : B,
      ee ((includeRight : B →ₐ[S] F ⊗[S] B) b) = (includeRight : B →ₐ[S] F ⊗[S] B) (e b) :=
  ⟨Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e, fun b => by
    rw [Algebra.TensorProduct.congr_apply, includeRight_apply, includeRight_apply, map_tmul]
    rfl⟩

theorem main
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (j₀ : B)
    [IsDomain ↥(Algebra.adjoin A ({j₀} : Set B))]
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({j₀} : Set B)) B)
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({j₀} : Set B)) B) 𝔭 = ⊥) :
    letI S := ↥(Algebra.adjoin A ({j₀} : Set B))
    letI F := FractionRing S
    letI R := F ⊗[S] B
    letI ιR : B →ₐ[S] R := Algebra.TensorProduct.includeRight
    (∀ 𝔓 : Ideal R, 𝔓.IsPrime → Ideal.comap ιR 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, ∃! 𝔓 : Ideal R, 𝔓.IsPrime ∧ Ideal.comap ιR 𝔓 = 𝔭) ∧
    (∀ e : B ≃ₐ[A] B, e j₀ = j₀ →
      ∃ ee : R ≃ₐ[F] R, ∀ b : B, ee (ιR b) = ιR (e b)) := by
  haveI := hint

  have hfix : ∀ (e : B ≃ₐ[A] B), e j₀ = j₀ → ∀ b ∈ Algebra.adjoin A ({j₀} : Set B), e b = b := by
    intro e he b hb
    have hle : Algebra.adjoin A ({j₀} : Set B) ≤ AlgHom.equalizer (e : B →ₐ[A] B) (AlgHom.id A B) :=
      Algebra.adjoin_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [SetLike.mem_coe, AlgHom.mem_equalizer]
        exact he)
    exact (AlgHom.mem_equalizer _ _ _).mp (hle hb)
  refine ⟨(parts12 hdom).1, (parts12 hdom).2, ?_⟩
  intro e he
  let eS : B ≃ₐ[↥(Algebra.adjoin A ({j₀} : Set B))] B :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => hfix e he s s.2)
  obtain ⟨ee, hee⟩ := part3 (F := FractionRing ↥(Algebra.adjoin A ({j₀} : Set B))) eS
  exact ⟨ee, fun b => hee b⟩

end DICT42

theorem solution
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (j₀ : B)
    [IsDomain ↥(Algebra.adjoin A ({j₀} : Set B))]
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({j₀} : Set B)) B)
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({j₀} : Set B)) B) 𝔭 = ⊥) :
    letI S := ↥(Algebra.adjoin A ({j₀} : Set B))
    letI F := FractionRing S
    letI R := F ⊗[S] B
    letI ιR : B →ₐ[S] R := Algebra.TensorProduct.includeRight
    (∀ 𝔓 : Ideal R, 𝔓.IsPrime → Ideal.comap ιR 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, ∃! 𝔓 : Ideal R, 𝔓.IsPrime ∧ Ideal.comap ιR 𝔓 = 𝔭) ∧
    (∀ e : B ≃ₐ[A] B, e j₀ = j₀ →
      ∃ ee : R ≃ₐ[F] R, ∀ b : B, ee (ιR b) = ιR (e b)) :=
  DICT42.main A B j₀ hint hdom

end S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary
end P2MW
export P2MW.S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary (solution)
