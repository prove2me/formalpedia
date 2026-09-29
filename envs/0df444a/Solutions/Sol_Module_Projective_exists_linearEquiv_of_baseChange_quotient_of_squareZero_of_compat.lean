-- Prove2me | solution 1 for Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6377f918-118f-52e9-b0e1-616df588e036

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

universe u

set_option autoImplicit false

open TensorProduct

namespace Module p2m_export "Module" "Injective mk restrictScalars Finite.fg_top jacobson Projective projective_lifting_property" namespace Projective p2m_export "Module.Projective" "mk" end Module.Projective
p2m_open_scoped "Module Module.Projective" in

private lemma Module.Projective.le_jacobson_bot_of_sq_eq_bot_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxx : x * x = 0 := by
    have hmem : x * x ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hx hx
    rw [hI] at hmem
    simpa using hmem
  have hxy : IsNilpotent (x * y) := ⟨2, by
    calc (x * y) ^ 2 = (x * x) * (y * y) := by ring
      _ = 0 := by rw [hxx, zero_mul]⟩
  exact hxy.isUnit_add_one

p2m_open_scoped "Module Module.Projective" in

private lemma Module.Projective.surjective_of_one_tmul_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {N M : Type u} [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    [Module.Finite R M] (f : N →ₗ[R] M)
    (hf : ∀ m : M, ∃ n : N, (1 : R ⧸ I) ⊗ₜ[R] f n = (1 : R ⧸ I) ⊗ₜ[R] m) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
  intro m _
  obtain ⟨n, hn⟩ := hf m
  have key : ∀ x : M, quotTensorEquivQuotSMul M I ((1 : R ⧸ I) ⊗ₜ[R] x) =
      Submodule.Quotient.mk x := by
    intro x
    rw [← map_one (Ideal.Quotient.mk I), quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have hq : (Submodule.Quotient.mk (f n) : M ⧸ (I • ⊤ : Submodule R M)) =
      Submodule.Quotient.mk m := by
    rw [← key, ← key, hn]
  have hmem : f n - m ∈ I • (⊤ : Submodule R M) := (Submodule.Quotient.eq _).mp hq
  have hsplit : m = f n - (f n - m) := by abel
  rw [hsplit]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self f n))
    (Submodule.mem_sup_right hmem)

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := by

  have hmk₁ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₁ 1) :=
    TensorProduct.mk_surjective R P₁ (R ⧸ I) Ideal.Quotient.mk_surjective
  have hmk₂ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₂ 1) :=
    TensorProduct.mk_surjective R P₂ (R ⧸ I) Ideal.Quotient.mk_surjective

  obtain ⟨f, hf⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₂ 1)
    ((e.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₁ 1) hmk₂
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₁ 1)
    ((e.symm.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₂ 1) hmk₁
  have hf' : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] f p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := fun p =>
    LinearMap.congr_fun hf p
  have hg' : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] g q = e.symm ((1 : R ⧸ I) ⊗ₜ[R] q) := fun q =>
    LinearMap.congr_fun hg q

  have hgf : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] (g ∘ₗ f) p = (1 : R ⧸ I) ⊗ₜ[R] p := fun p => by
    rw [LinearMap.comp_apply, hg', hf', LinearEquiv.symm_apply_apply]
  have hfg : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] (f ∘ₗ g) q = (1 : R ⧸ I) ⊗ₜ[R] q := fun q => by
    rw [LinearMap.comp_apply, hf', hg', LinearEquiv.apply_symm_apply]

  have hJ := Module.Projective.le_jacobson_bot_of_sq_eq_bot_aux I hI
  have sgf : Function.Surjective (g ∘ₗ f) :=
    Module.Projective.surjective_of_one_tmul_aux I hJ (g ∘ₗ f) fun p => ⟨p, hgf p⟩
  have sfg : Function.Surjective (f ∘ₗ g) :=
    Module.Projective.surjective_of_one_tmul_aux I hJ (f ∘ₗ g) fun q => ⟨q, hfg q⟩

  have igf : Function.Injective (g ∘ₗ f) :=
    OrzechProperty.injective_of_surjective_endomorphism _ sgf
  rw [LinearMap.coe_comp] at igf sfg
  have hbij : Function.Bijective f := ⟨igf.of_comp, sfg.of_comp⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun p => hf' p⟩

end S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
end P2MW
export P2MW.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat (solution)
