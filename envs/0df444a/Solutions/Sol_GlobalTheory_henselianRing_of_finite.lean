-- Prove2me | solution 1 for GlobalTheory.henselianRing_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:52.587462+00:00
-- url     : https://prove2.me/submissions/7fe36fb6-8eff-4de2-8222-a3539ef1616e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_mk_of_le_jacobson
import Theorems.Thm_GlobalTheory_exists_idempotent_lift_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (J : Ideal S)
    (hJ : J ≤ (⊥ : Ideal S).jacobson) : HenselianRing S J where
  jac := hJ
  is_henselian f hf a₀ h₁ h₂ := by
    nontriviality S using Subsingleton.elim _ (0 : S)
    obtain ⟨u, hu⟩ := (isUnit_of_isUnit_mk_of_le_jacobson hJ h₂).exists_left_inv
    set g := f /ₘ (X - C a₀) with hg
    have hfg : (X - C a₀) * g = f - C (f.eval a₀) := by
      rw [hg, X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval]
    have hga : u * g.eval a₀ = 1 := by
      have := congr((derivative $hfg).eval a₀)
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
        eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_one, eval_zero, sub_zero,
        one_mul] at this
      rw [this, hu]
    have hdeg : g.degree < f.degree :=
      degree_divByMonic_lt f _ hf.ne_zero (by simp)
    let T := AdjoinRoot f
    have : Module.Finite S T := hf.finite_adjoinRoot
    have : Module.Finite R T := .trans S T
    let x : T := AdjoinRoot.root f
    let JT : Ideal T := J.map (algebraMap S T)
    let e₀ : T := u • aeval x g
    have hx0 : (x - algebraMap S T a₀) * e₀ ∈ JT := by
      have := congr(aeval x $hfg)
      simp only [map_mul, map_sub, aeval_X, aeval_C] at this
      rw [mul_smul_comm, this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_sub, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_map_of_mem _ h₁))
    have hdvd : ∀ (p : S[X]) (a : S),
        x - algebraMap S T a ∣ aeval x p - algebraMap S T (p.eval a) := fun p a ↦ by
      rw [← aeval_algebraMap_apply_eq_algebraMap_eval, ← eval_map_algebraMap,
        ← eval_map_algebraMap]
      exact sub_dvd_eval_sub _ _ _
    have hp0 : ∀ p : S[X], (aeval x p - algebraMap S T (p.eval a₀)) * e₀ ∈ JT := fun p ↦ by
      obtain ⟨c, hc⟩ : x - algebraMap S T a₀ ∣ aeval x p - algebraMap S T (p.eval a₀) := by
        exact hdvd p a₀
      rw [hc, mul_right_comm]
      exact Ideal.mul_mem_right _ _ hx0
    have he₀ : IsIdempotentElem (Ideal.Quotient.mk JT e₀) := by
      rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
      have := hp0 (C u * g)
      rw [eval_mul, eval_C, hga, map_one, map_mul, aeval_C, ← Algebra.smul_def, sub_mul,
        one_mul] at this
      exact this
    obtain ⟨e, he, hee⟩ := exists_idempotent_lift_of_henselian R (Ideal.Quotient.mk JT)
      Ideal.Quotient.mk_surjective he₀
    rw [Ideal.Quotient.eq] at hee
    have hJT : ∀ y ∈ JT, y ∈ J • (⊤ : Submodule S T) := fun y hy ↦ by
      rw [Ideal.smul_top_eq_map]; exact hy
    have hp : ∀ p : S[X], (aeval x p - algebraMap S T (p.eval a₀)) * e ∈ JT := fun p ↦ by
      have := add_mem (hp0 p) (Ideal.mul_mem_left _ (aeval x p - algebraMap S T (p.eval a₀)) hee)
      rwa [← mul_add, add_sub_cancel] at this
    let μ : T →ₗ[S] T := LinearMap.mulRight S e
    have hle : (⊤ : Submodule S T).map μ ≤ Submodule.span S {e} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top.map _) hJ ?_
      rintro _ ⟨y, -, rfl⟩
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [← AdjoinRoot.aeval_eq]
      refine Submodule.mem_sup.2 ⟨p.eval a₀ • e,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        μ ((aeval x p - algebraMap S T (p.eval a₀)) * e), ?_, ?_⟩
      · rw [← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem (hJT _ (hp p))
      · simp only [μ, LinearMap.mulRight_apply, mul_assoc, he.eq, Algebra.smul_def]
        ring
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle (Submodule.mem_map_of_mem
      (Submodule.mem_top (x := x))))
    simp only [μ, LinearMap.mulRight_apply, Algebra.smul_def] at ha
    let l : T →ₗ[S] S := (leval a₀).comp (AdjoinRoot.modByMonicHom hf)
    have hlJ : ∀ y ∈ JT, l y ∈ J := fun y hy ↦ by
      have := Submodule.mem_map_of_mem (f := l) (hJT y hy)
      rw [Submodule.map_smul''] at this
      have h2 := Submodule.smul_mono (le_refl J) (le_top (a := (⊤ : Submodule S T).map l)) this
      simpa using h2
    have hl0 : l e₀ = 1 := by
      simp only [e₀, map_smul, l, LinearMap.comp_apply, x]
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).2 hdeg]
      simpa using hga
    have hle : IsUnit (l e) := by
      have := hlJ _ hee
      rw [map_sub, hl0] at this
      simpa using Ideal.mem_jacobson_bot.1 (hJ this) 1
    refine ⟨a, ?_, ?_⟩
    · obtain ⟨c, hc⟩ : x - algebraMap S T a ∣ aeval x f - algebraMap S T (f.eval a) := by
        exact hdvd f a
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self] at hc
      have : f.eval a • e = 0 := by
        rw [Algebra.smul_def]
        linear_combination (-e) * hc + c * ha
      have := congr(l $this)
      rw [map_smul, map_zero, smul_eq_mul] at this
      exact hle.mul_left_eq_zero.1 this
    · have := hp X
      rw [aeval_X, eval_X, sub_mul, ← ha, ← sub_mul, ← map_sub, ← Algebra.smul_def] at this
      have := hlJ _ this
      rw [map_smul, smul_eq_mul] at this
      exact (Ideal.mul_unit_mem_iff_mem _ hle).1 this
end GlobalTheory
