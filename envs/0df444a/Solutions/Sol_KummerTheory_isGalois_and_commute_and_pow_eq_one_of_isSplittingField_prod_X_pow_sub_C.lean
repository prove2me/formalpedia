-- Prove2me | solution 1 for KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7a125441-3d43-5f8a-a4f2-c66eb7a58c29

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C

set_option autoImplicit false

theorem solution
    (K L : Type*) [Field K] [Field L] [Algebra K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty)
    (S : Finset Kˣ) [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))] :
    IsGalois K L ∧ (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧ ∀ σ : L ≃ₐ[K] L, σ ^ n = 1 := by
  classical
  obtain ⟨ζ, hζmem⟩ := hμ
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hζmem)
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots hnpos).1 hζmem
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hnK : (n : K) ≠ 0 := (IsPrimitiveRoot.neZero' hζ).ne
  set f : Polynomial K := ∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)) with hf
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective

  have hsep : f.Separable := by
    rw [hf]
    refine Polynomial.separable_prod' ?_ ?_
    · intro u _ v _ huv
      have hvu : (v : K) - u ≠ 0 := sub_ne_zero.2 (fun h => huv (Units.ext h).symm)
      refine ⟨Polynomial.C ((v : K) - u)⁻¹, -Polynomial.C ((v : K) - u)⁻¹, ?_⟩
      calc Polynomial.C ((v : K) - u)⁻¹ * (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K))
            + -Polynomial.C ((v : K) - u)⁻¹ * (Polynomial.X ^ n - Polynomial.C ((v : Kˣ) : K))
          = Polynomial.C ((v : K) - u)⁻¹ * (Polynomial.C (v : K) - Polynomial.C (u : K)) := by ring
        _ = 1 := by rw [← Polynomial.C_sub, ← Polynomial.C_mul, inv_mul_cancel₀ hvu, Polynomial.C_1]
    · intro u _
      exact Polynomial.separable_X_pow_sub_C (u : K) hnK u.ne_zero
  have hGal : IsGalois K L := IsGalois.of_separable_splitting_field hsep

  have hroots : ∀ (σ : L ≃ₐ[K] L), ∀ α ∈ f.rootSet L, ∃ i : ℕ, σ α = (algebraMap K L ζ) ^ i * α := by
    intro σ α hα
    rw [Polynomial.mem_rootSet] at hα
    obtain ⟨-, hα⟩ := hα
    rw [hf, map_prod, Finset.prod_eq_zero_iff] at hα
    obtain ⟨u, hu, hαu⟩ := hα
    have hαn : α ^ n = algebraMap K L (u : K) := by
      rw [← sub_eq_zero]
      simpa using hαu
    have hβ : (σ α) ^ n = algebraMap K L (u : K) := by rw [← map_pow, hαn, AlgEquiv.commutes]
    have hmem : σ α ∈ Polynomial.nthRoots n (algebraMap K L (u : K)) :=
      (Polynomial.mem_nthRoots hnpos).2 hβ
    rw [hζL.nthRoots_eq hαn, Multiset.mem_map] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact ⟨i, hi.symm⟩
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet L f
  have hfix : ∀ (σ : L ≃ₐ[K] L) (i : ℕ), σ ((algebraMap K L ζ) ^ i) = (algebraMap K L ζ) ^ i :=
    fun σ i => by rw [map_pow, AlgEquiv.commutes]
  refine ⟨hGal, ?_, ?_⟩
  · intro σ τ
    apply AlgEquiv.ext
    intro x
    have key : ((σ * τ : L ≃ₐ[K] L) : L →ₐ[K] L) = ((τ * σ : L ≃ₐ[K] L) : L →ₐ[K] L) := by
      apply AlgHom.ext_of_adjoin_eq_top hadj
      intro α hα
      obtain ⟨i, hi⟩ := hroots σ α hα
      obtain ⟨j, hj⟩ := hroots τ α hα
      change (σ * τ) α = (τ * σ) α
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hj, map_mul, hi, hfix, map_mul, hj, hfix]
      ring
    exact DFunLike.congr_fun key x
  · intro σ
    apply AlgEquiv.ext
    intro x
    have key : ((σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) = AlgHom.id K L := by
      apply AlgHom.ext_of_adjoin_eq_top hadj
      intro α hα
      obtain ⟨i, hi⟩ := hroots σ α hα
      have hk : ∀ k : ℕ, (σ ^ k) α = (algebraMap K L ζ) ^ (i * k) * α := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, AlgEquiv.mul_apply, hi, map_mul, hfix, ih, ← mul_assoc, ← pow_add,
            show i + i * k = i * (k + 1) by ring]
      change (σ ^ n) α = α
      rw [hk n, mul_comm i n, pow_mul, hζL.pow_eq_one, one_pow, one_mul]
    exact DFunLike.congr_fun key x

end S_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C
end P2MW
export P2MW.S_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C (solution)
