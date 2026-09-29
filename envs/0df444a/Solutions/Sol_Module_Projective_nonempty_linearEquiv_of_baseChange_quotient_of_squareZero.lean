-- Prove2me | solution 1 for Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e32a9c0f-f895-5e97-befb-7fff8b48c9e4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

universe u

set_option autoImplicit false
set_option maxHeartbeats 6400000

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    Nonempty (P₁ ≃ₗ[R] P₂) := by
  classical
  have hIjac : I ≤ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson_bot]
    refine le_trans (fun a ha => ?_) (nilradical_le_jacobson R)
    exact ⟨2, by have := Ideal.pow_mem_pow ha 2; rw [hI] at this; simpa using this⟩

  have hB : ∀ {P : Type u} [AddCommGroup P] [Module R P] (p : P),
      (1 : R⧸I) ⊗ₜ[R] p = 0 → p ∈ I • (⊤ : Submodule R P) := by
    intro P _ _ p hp
    rw [← Submodule.Quotient.mk_eq_zero]
    have h1 : (quotTensorEquivQuotSMul P I) ((1 : R⧸I) ⊗ₜ[R] p) = Submodule.Quotient.mk p := by
      have := quotTensorEquivQuotSMul_mk_tmul I (1 : R) p
      simpa using this
    rw [← h1, hp, map_zero]
  let q₁ : P₁ →ₗ[R] (R ⧸ I) ⊗[R] P₁ := (TensorProduct.mk R (R ⧸ I) P₁) 1
  let q₂ : P₂ →ₗ[R] (R ⧸ I) ⊗[R] P₂ := (TensorProduct.mk R (R ⧸ I) P₂) 1
  have hqsurj : ∀ {P : Type u} [AddCommGroup P] [Module R P],
      Function.Surjective ((TensorProduct.mk R (R ⧸ I) P) 1) := by
    intro P _ _ z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r p =>
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨r' • p, ?_⟩
      simp only [TensorProduct.mk_apply]
      rw [← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨px, hpx⟩ := hx; obtain ⟨py, hpy⟩ := hy
      exact ⟨px + py, by simp only [map_add, hpx, hpy]⟩
  obtain ⟨f, hf⟩ :=
    Module.projective_lifting_property q₂ ((e.toLinearMap.restrictScalars R).comp q₁) hqsurj
  obtain ⟨f', hf'⟩ :=
    Module.projective_lifting_property q₁ ((e.symm.toLinearMap.restrictScalars R).comp q₂) hqsurj
  have hff' : ∀ p, q₁ (f' (f p)) = q₁ p := fun p => by
    have h1 : q₂ (f p) = e (q₁ p) := by
      have := congrFun (congrArg DFunLike.coe hf) p; simpa [q₁, q₂] using this
    have h2 : q₁ (f' (f p)) = e.symm (q₂ (f p)) := by
      have := congrFun (congrArg DFunLike.coe hf') (f p); simpa [q₁, q₂] using this
    rw [h2, h1, LinearEquiv.symm_apply_apply]
  have hf'f : ∀ p, q₂ (f (f' p)) = q₂ p := fun p => by
    have h1 : q₁ (f' p) = e.symm (q₂ p) := by
      have := congrFun (congrArg DFunLike.coe hf') p; simpa [q₁, q₂] using this
    have h2 : q₂ (f (f' p)) = e (q₁ (f' p)) := by
      have := congrFun (congrArg DFunLike.coe hf) (f' p); simpa [q₁, q₂] using this
    rw [h2, h1, LinearEquiv.apply_symm_apply]
  have hA : ∀ {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P]
      (N : Submodule R P), N ⊔ I • ⊤ = ⊤ → N = ⊤ := by
    intro P _ _ _ N h
    refine le_antisymm le_top ?_
    exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIjac
      (le_of_eq h.symm)
  have hff'_surj : Function.Surjective (f'.comp f) := by
    rw [← LinearMap.range_eq_top]
    refine hA _ ?_
    rw [eq_top_iff]; intro p _
    have hmem : p - f' (f p) ∈ I • (⊤ : Submodule R P₁) := by
      refine hB _ ?_
      have : q₁ (p - f' (f p)) = 0 := by rw [map_sub, hff' p, sub_self]
      simpa only [q₁, TensorProduct.mk_apply] using this
    exact Submodule.mem_sup.mpr ⟨f' (f p), LinearMap.mem_range.mpr ⟨p, rfl⟩,
      p - f' (f p), hmem, by abel⟩
  have hf'f_surj : Function.Surjective (f.comp f') := by
    rw [← LinearMap.range_eq_top]
    refine hA _ ?_
    rw [eq_top_iff]; intro p _
    have hmem : p - f (f' p) ∈ I • (⊤ : Submodule R P₂) := by
      refine hB _ ?_
      have : q₂ (p - f (f' p)) = 0 := by rw [map_sub, hf'f p, sub_self]
      simpa only [q₂, TensorProduct.mk_apply] using this
    exact Submodule.mem_sup.mpr ⟨f (f' p), LinearMap.mem_range.mpr ⟨p, rfl⟩,
      p - f (f' p), hmem, by abel⟩
  have hf_bij : Function.Bijective f :=
    ⟨fun a b hab =>
      (OrzechProperty.injective_of_surjective_endomorphism (f'.comp f) hff'_surj)
        (by simp only [LinearMap.comp_apply, hab]),
     fun p => let ⟨q, hq⟩ := hf'f_surj p; ⟨f' q, by simpa [LinearMap.comp_apply] using hq⟩⟩
  exact ⟨LinearEquiv.ofBijective f hf_bij⟩

end S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
end P2MW
export P2MW.S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero (solution)
