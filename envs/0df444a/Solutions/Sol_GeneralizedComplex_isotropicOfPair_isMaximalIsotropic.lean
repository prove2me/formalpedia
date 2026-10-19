-- Prove2me | solution 1 for GeneralizedComplex.isotropicOfPair_isMaximalIsotropic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:33:22.730687+00:00
-- url     : https://prove2.me/submissions/96114983-40c6-4c3a-840a-2d2ed3f1f4ca

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GCAux4
open GeneralizedComplex

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

/-- `ξ ↦ (Y ↦ ξ ⬝ Y)` -/
def φ {𝕜 : Type*} [Field 𝕜] {N : ℕ} (E : Submodule 𝕜 (Fin N → 𝕜)) :
    (Fin N → 𝕜) →ₗ[𝕜] (E →ₗ[𝕜] 𝕜) :=
  LinearMap.mk₂ 𝕜 (fun ξ (Y : E) => ξ ⬝ᵥ (Y : Fin N → 𝕜))
    (fun a b Y => add_dotProduct _ _ _) (fun c a Y => smul_dotProduct _ _ _)
    (fun a Y Z => by simp [dotProduct_add]) (fun c a Y => by simp [dotProduct_smul])

lemma finrank_ker_φ {𝕜 : Type*} [Field 𝕜] {N : ℕ} (E : Submodule 𝕜 (Fin N → 𝕜)) :
    Module.finrank 𝕜 (LinearMap.ker (φ E)) + Module.finrank 𝕜 E = N := by
  have hs : LinearMap.range (φ E) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro f
    obtain ⟨ξ, hξ⟩ := exists_covector E f
    exact ⟨ξ, LinearMap.ext fun Y => hξ Y⟩
  have h := LinearMap.finrank_range_add_finrank_ker (φ E)
  rw [hs, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h
  omega

theorem main {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (E : Submodule 𝕜 (Fin N → 𝕜)) (ε : LinearMap.BilinForm 𝕜 E)
    (hε : ∀ X Y : E, ε X Y = -ε Y X) :
    IsMaximalIsotropic (isotropicOfPair E ε) := by
  set L := isotropicOfPair E ε
  constructor
  · rintro u ⟨hu, hu'⟩ v ⟨hv, hv'⟩
    unfold pairing
    rw [hu' ⟨_, hv⟩, hv' ⟨_, hu⟩, hε]
    simp
  · let ψ : L →ₗ[𝕜] E :=
      { toFun := fun u => ⟨vecPart (u : GIdx N → 𝕜), u.2.1⟩
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    have hψ : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro X
      obtain ⟨ξ, hξ⟩ := exists_covector E (ε X)
      exact ⟨⟨Sum.elim (X : Fin N → 𝕜) ξ, X.2, fun Y => hξ Y⟩, rfl⟩
    let κ : LinearMap.ker (φ E) →ₗ[𝕜] L :=
      { toFun := fun ξ => ⟨Sum.elim 0 ξ.1, E.zero_mem, fun Y => by
          have h0 : (⟨vecPart (Sum.elim (0 : Fin N → 𝕜) ξ.1), E.zero_mem⟩ : E) = 0 := rfl
          rw [h0, map_zero, LinearMap.zero_apply]
          have := LinearMap.congr_fun (LinearMap.mem_ker.1 ξ.2) Y
          exact this⟩
        map_add' := fun a b => by
          apply Subtype.ext; ext i; cases i <;> simp
        map_smul' := fun c a => by
          apply Subtype.ext; ext i; cases i <;> simp }
    have hκ : Function.Injective κ := by
      intro a b hab
      apply Subtype.ext; ext i
      have := congrFun (congrArg Subtype.val hab) (Sum.inr i)
      simpa [κ] using this
    have hker : LinearMap.ker ψ = LinearMap.range κ := by
      ext u
      simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hu
        have hv : vecPart (u : GIdx N → 𝕜) = 0 := congrArg Subtype.val hu
        refine ⟨⟨formPart (u : GIdx N → 𝕜), ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker]
          ext Y
          have := u.2.2 Y
          have h0 : (⟨vecPart (u : GIdx N → 𝕜), u.2.1⟩ : E) = 0 := Subtype.ext hv
          rw [h0, map_zero, LinearMap.zero_apply] at this
          exact this
        · apply Subtype.ext; ext i
          cases i with
          | inl i => exact (congrFun hv i).symm
          | inr i => rfl
      · rintro ⟨ξ, rfl⟩
        rfl
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hψ, finrank_top, hker, LinearMap.finrank_range_of_inj hκ] at h1
    have h2 := finrank_ker_φ E
    omega

end GCAux4

open GeneralizedComplex in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (E : Submodule 𝕜 (Fin N → 𝕜)) (ε : LinearMap.BilinForm 𝕜 E)
    (hε : ∀ X Y : E, ε X Y = -ε Y X) :
    IsMaximalIsotropic (isotropicOfPair E ε) := GCAux4.main E ε hε
