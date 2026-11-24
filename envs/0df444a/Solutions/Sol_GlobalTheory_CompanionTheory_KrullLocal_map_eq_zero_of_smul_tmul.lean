-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KrullLocal.map_eq_zero_of_smul_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:03:22.103811+00:00
-- url     : https://prove2.me/submissions/b3d016ad-e2a8-4415-a724-85cd536d616e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
import Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_exists_ringHom_of_fractions
import Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_exists_mul_eq_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal
namespace GlobalTheory.CompanionTheory.KrullLocal
theorem _root_.solution {B R C M D N : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [CommRing D] [Algebra R D]
    [AddCommGroup N] [Module R N] [Module D N] [IsScalarTower R D N]
    (J : Ideal B) (hJ : ∀ a ∈ J, algebraMap R D (algebraMap B R a) = 0)
    (Q₀ : Ideal (R ⊗[B] C)) (hQ : Q₀.IsPrime)
    (hunit : ∀ r : R, r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) →
      IsUnit (algebraMap R D r))
    (h1 : ∀ c : C, ∃ b t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * algebraMap B C b = 0) → ∃ t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      t * b ∈ J)
    (ι : M →ₗ[R] N) (y : M) (w : R ⊗[B] C) (hw0 : w ∉ Q₀)
    (hw : w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0) : ι y = 0 := by
  set q : Ideal C := Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) with hqdef
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hLR : ∀ t : B, (algebraMap B R t) ⊗ₜ[B] (1 : C) = (1 : R) ⊗ₜ[B] algebraMap B C t := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hmemq : ∀ c : C, c ∈ q ↔ (1 : R) ⊗ₜ[B] c ∈ Q₀ := fun c => Iff.rfl
  have hmemp : ∀ r : R, r ∈ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ↔
      r ⊗ₜ[B] (1 : C) ∈ Q₀ := fun r => Iff.rfl
  let φ₀ : B →+* D := (algebraMap R D).comp (algebraMap B R)
  have hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ₀ t) := by
    intro t ht
    apply hunit
    rw [hmemp, hLR]
    exact fun h => ht ((hmemq _).2 h)
  have h1' : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b := h1
  obtain ⟨g, hg, hgu⟩ := exists_ringHom_of_fractions q φ₀ hu h1' (by
    intro b hb
    obtain ⟨t, ht, htb⟩ := h2 b hb
    have e : φ₀ (t * b) = 0 := hJ _ htb
    rw [map_mul] at e
    exact (hu t ht).mul_right_eq_zero.1 e)
  letI : Algebra B D := φ₀.toAlgebra
  haveI : IsScalarTower B R D := .of_algebraMap_eq (fun _ => rfl)
  let gA : C →ₐ[B] D := { g with commutes' := hg }
  let fA : R →ₐ[B] D := IsScalarTower.toAlgHom B R D
  let φ : R ⊗[B] C →ₐ[B] D := Algebra.TensorProduct.productMap fA gA
  have hφ : ∀ (r : R) (c : C), φ (r ⊗ₜ[B] c) = algebraMap R D r * g c := by
    intro r c
    simp [φ, fA, gA]
  have hφr : ∀ (r : R) (τ : R ⊗[B] C), φ (r • τ) = algebraMap R D r * φ τ := by
    intro r τ
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  let Ψ : (R ⊗[B] C) ⊗[R] M →ₗ[R] N := TensorProduct.lift (LinearMap.mk₂ R
    (fun (τ : R ⊗[B] C) (m : M) => φ τ • ι m)
    (fun a b m => by simp [add_smul])
    (fun r a m => by rw [hφr, mul_smul, algebraMap_smul])
    (fun a m n => by simp)
    (fun r a m => by rw [map_smul, smul_comm]))
  have hΨ : φ w • ι y = 0 := by
    have e := congrArg Ψ hw
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zero] at e
    simpa [Ψ] using e
  obtain ⟨s, v, r, hs, hv, e⟩ := exists_mul_eq_tmul (R := R) q h1' w
  have hr : r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) := by
    intro hm
    rw [hmemp] at hm
    have h3 : (r ⊗ₜ[B] v) ∈ Q₀ := by
      have := Q₀.mul_mem_right ((1 : R) ⊗ₜ[B] v) hm
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
    rw [← e] at h3
    rcases hQ.mem_or_mem h3 with h4 | h4
    · have : v * algebraMap B C s ∈ q := (hmemq _).2 h4
      exact (hq.mem_or_mem this).elim hv hs
    · exact hw0 h4
  have hunitw : IsUnit (φ w) := by
    have e2 := congrArg φ e
    rw [map_mul, hφ, hφ] at e2
    have hU : IsUnit (algebraMap R D r * g v) := (hunit r hr).mul (hgu v hv)
    rw [← e2] at hU
    exact isUnit_of_mul_isUnit_right hU
  obtain ⟨u, hu'⟩ := hunitw
  have : ι y = (↑u⁻¹ : D) • (φ w • ι y) := by
    rw [← hu', smul_smul, Units.inv_mul, one_smul]
  rw [this, hΨ, smul_zero]
end GlobalTheory.CompanionTheory.KrullLocal
