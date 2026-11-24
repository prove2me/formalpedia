-- Prove2me | solution 1 for GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:33.498515+00:00
-- url     : https://prove2.me/submissions/1b611bb6-722d-4f4b-9b81-15a2685f7fe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensor
import Theorems.Thm_GlobalTheory_exists_base_denominator_of_finite
import Theorems.Thm_GlobalTheory_finite_fractionRing_of_finite

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
theorem _root_.solution (T U C F K L : Type) [CommRing T] [IsDomain T]
    [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K]
    [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L]
    [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C]
    (φ : U ⊗[T] C →+* L ⊗[F] K) (hinj : Function.Injective φ)
    (hφ : ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) :
    ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  have hTU : ∀ t : T, t ≠ 0 → algebraMap T U t ≠ 0 := by
    intro t ht h0
    have h1 : algebraMap T L t = 0 := by
      rw [IsScalarTower.algebraMap_apply T U L, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply T F L] at h1
    apply ht
    simpa using h1
  have den : ∀ ω : L ⊗[F] K, ∃ u : U, u ≠ 0 ∧ ∃ s', φ (u ⊗ₜ 1) * ω = φ s' := by
    intro ω
    induction ω using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul l k =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := U) l
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbL : algebraMap U L b ≠ 0 := by simpa using hb0
      obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
      refine ⟨algebraMap T U t * b, mul_ne_zero (hTU t ht) hb0, a ⊗ₜ c, ?_⟩
      rw [hφ, hφ, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hc,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def (algebraMap T F t) k,
        ← TensorProduct.smul_tmul,
        Algebra.smul_def, ← IsScalarTower.algebraMap_apply T F L, map_mul,
        ← IsScalarTower.algebraMap_apply T U L]
      congr 1
      field_simp
    | add x y hx hy =>
      obtain ⟨u, hu, s₁, h₁⟩ := hx
      obtain ⟨v, hv, s₂, h₂⟩ := hy
      refine ⟨u * v, mul_ne_zero hu hv, (v ⊗ₜ 1) * s₁ + (u ⊗ₜ 1) * s₂, ?_⟩
      have : ((u * v) ⊗ₜ[T] (1 : C)) = (u ⊗ₜ 1) * (v ⊗ₜ 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this, map_add, map_mul, map_mul, map_mul, ← h₁, ← h₂]
      ring
  have : Module.Finite F K := finite_fractionRing_of_finite T C F K
  have : IsArtinianRing (L ⊗[F] K) := IsArtinianRing.of_finite L (L ⊗[F] K)
  intro s hs
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro ω hω
  obtain ⟨u, hu, s', h⟩ := den ω
  have h0 : s' * s = 0 := by
    apply hinj
    rw [map_mul, ← h, mul_assoc, hω, mul_zero, map_zero]
  have hs' : s' = 0 := (mem_nonZeroDivisors_iff_right.1 hs) s' h0
  have huL : algebraMap U L u ≠ 0 := by simpa using hu
  have hunit : IsUnit (φ (u ⊗ₜ 1)) := by
    rw [hφ, map_one]
    exact (IsUnit.mk0 _ huL).map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := L) (B := K))
  rw [hs', map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h
end GlobalTheory
