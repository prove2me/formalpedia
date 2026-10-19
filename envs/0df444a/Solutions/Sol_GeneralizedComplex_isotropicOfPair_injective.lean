-- Prove2me | solution 1 for GeneralizedComplex.isotropicOfPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:32:22.279413+00:00
-- url     : https://prove2.me/submissions/4e2b5215-9821-44e2-b288-7cfeb241ac59

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GCAux3
open GeneralizedComplex

/-- every linear functional on a subspace of `𝕜^N` is a dot product with some covector -/
lemma exists_covector {𝕜 : Type*} [Field 𝕜] {N : ℕ} (E : Submodule 𝕜 (Fin N → 𝕜))
    (f : E →ₗ[𝕜] 𝕜) : ∃ ξ : Fin N → 𝕜, ∀ Y : E, ξ ⬝ᵥ (Y : Fin N → 𝕜) = f Y := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨fun i => g (Pi.single i 1), fun Y => ?_⟩
  rw [← hg]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  conv_rhs => rw [pi_eq_sum_univ (Y : Fin N → 𝕜)]
  rw [map_sum]
  simp only [map_smul, dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  ext j; simp [Pi.single_apply, eq_comm]

lemma mem_of {𝕜 : Type*} [Field 𝕜] {N : ℕ} (E : Submodule 𝕜 (Fin N → 𝕜))
    (ε : LinearMap.BilinForm 𝕜 E) (X : E) (ξ : Fin N → 𝕜)
    (hξ : ∀ Y : E, ξ ⬝ᵥ (Y : Fin N → 𝕜) = ε X Y) :
    (Sum.elim (X : Fin N → 𝕜) ξ : GIdx N → 𝕜) ∈ isotropicOfPair E ε :=
  ⟨X.2, fun Y => hξ Y⟩

theorem main {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (E : Submodule 𝕜 (Fin N → 𝕜)) (ε ε' : LinearMap.BilinForm 𝕜 E) :
    tangentProjection (isotropicOfPair E ε) = E ∧
      (isotropicOfPair E ε = isotropicOfPair E ε' → ε = ε') := by
  constructor
  · ext X
    simp only [tangentProjection, Submodule.mem_map]
    constructor
    · rintro ⟨u, ⟨hu, -⟩, rfl⟩
      exact hu
    · intro hX
      obtain ⟨ξ, hξ⟩ := exists_covector E (ε ⟨X, hX⟩)
      exact ⟨_, mem_of E ε ⟨X, hX⟩ ξ hξ, by ext i; simp [LinearMap.funLeft_apply]⟩
  · intro h
    ext X Y
    obtain ⟨ξ, hξ⟩ := exists_covector E (ε X)
    have hm := mem_of E ε X ξ hξ
    rw [h] at hm
    obtain ⟨hX, hX'⟩ := hm
    have e1 := hX' Y
    have e2 := hξ Y
    rw [← e2]
    exact e1

end GCAux3

open GeneralizedComplex in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (E : Submodule 𝕜 (Fin N → 𝕜)) (ε ε' : LinearMap.BilinForm 𝕜 E) :
    tangentProjection (isotropicOfPair E ε) = E ∧
      (isotropicOfPair E ε = isotropicOfPair E ε' → ε = ε') := GCAux3.main E ε ε'
