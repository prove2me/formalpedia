-- Prove2me | solution 1 for GlobalTheory.mem_span_map_of_eval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:32.061802+00:00
-- url     : https://prove2.me/submissions/d842fa33-a8a6-4e0d-b9ee-9759f66d2d67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] [Infinite k] (σ τ : Type)
    (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k) (hD : D ≠ 0)
    (P : MvPolynomial σ (MvPolynomial τ k))
    (hP : ∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) :
    P ∈ Submodule.span (MvPolynomial τ k)
      (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  classical
  let Γ : Finset (τ →₀ ℕ) := P.support.biUnion (fun m => (coeff m P).support)
  let Q : (τ →₀ ℕ) → MvPolynomial σ k := fun γ =>
    ∑ m ∈ P.support, monomial m (coeff γ (coeff m P))
  have hQ : ∀ γ m, coeff m (Q γ) = coeff γ (coeff m P) := by
    intro γ m
    simp only [Q, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, coeff_zero]
  have hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ) := by
    ext m : 1
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]
    have : ∀ γ, (monomial γ (1 : k) : MvPolynomial τ k) * C (coeff γ (coeff m P)) = monomial γ (coeff γ (coeff m P)) := by
      intro γ; rw [mul_comm, C_mul_monomial, mul_one]
    simp only [this]
    by_cases hm : m ∈ P.support
    · conv_lhs => rw [as_sum (coeff m P)]
      apply Finset.sum_subset
      · intro γ hγ; exact Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩
      · intro γ _ hγ; rw [notMem_support_iff.mp hγ, monomial_zero]
    · rw [notMem_support_iff.mp hm]
      simp only [coeff_zero, monomial_zero, Finset.sum_const_zero]
  have hevid : ∀ y : τ → k, (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    intro y; ext c; simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]
  have hevP : ∀ y : τ → k, map (eval y) P =
      ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ := by
    intro y
    conv_lhs => rw [hdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]
  have hQM : ∀ γ ∈ Γ, Q γ ∈ M := by
    intro β hβ
    by_contra hnot
    obtain ⟨L, hLβ, hLM⟩ := Submodule.exists_le_ker_of_notMem hnot
    let R : MvPolynomial τ k := ∑ γ ∈ Γ, monomial γ (L (Q γ))
    have hR : ∀ y : τ → k, eval y R = L (map (eval y) P) := by
      intro y
      rw [hevP, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]
    have hRD : R * D = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_zero]
      by_cases hy : eval y D = 0
      · rw [hy, mul_zero]
      · rw [hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]
    have hR0 : R = 0 := (mul_eq_zero.mp hRD).resolve_right hD
    have hcoef : coeff β R = L (Q β) := by
      simp only [R, coeff_sum, coeff_monomial]
      rw [Finset.sum_ite_eq', if_pos hβ]
    exact hLβ (by rw [← hcoef, hR0, coeff_zero])
  suffices h : (∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)) ∈
      Submodule.span (MvPolynomial τ k)
        (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) by
    rwa [← hdec] at h
  refine Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨Q γ, hQM γ hγ, rfl⟩
end GlobalTheory
