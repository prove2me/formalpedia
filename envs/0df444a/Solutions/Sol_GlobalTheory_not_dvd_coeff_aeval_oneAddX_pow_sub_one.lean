-- Prove2me | solution 1 for GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:18.168548+00:00
-- url     : https://prove2.me/submissions/e28d12aa-7ad3-4809-98a4-f9a8abeead8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
namespace GlobalTheory
open scoped BigOperators in
private theorem C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd {O σ : Type} [CommRing O] [Fintype σ] (ϖ : O)
    (g : σ → Polynomial O) (k : σ → ℕ) (hg : ∀ q, Polynomial.C ϖ ∣ g q - Polynomial.X ^ k q)
    (m : σ → ℕ) :
    Polynomial.C ϖ ∣ ∏ q, g q ^ m q - Polynomial.X ^ (∑ q, m q * k q) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hq := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hg q))
  rw [map_pow, hq, ← map_pow, ← pow_mul, mul_comm]
open scoped BigOperators in
private theorem C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow {O : Type} [CommRing O] (ϖ : O) (l e : ℕ)
    (hl : l.Prime) (h : ϖ ∣ (l : O)) :
    Polynomial.C ϖ ∣ (1 + Polynomial.X : Polynomial O) ^ (l ^ e) - 1 - Polynomial.X ^ (l ^ e) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_X_pow]
  have hN : l ^ e ≠ 0 := (pow_pos hl.pos _).ne'
  by_cases h0 : i = 0
  · subst h0
    simp [hN.symm]
  by_cases hN' : i = l ^ e
  · subst hN'
    simp [h0, hl.ne_zero]
  · simp only [h0, hN', if_false, sub_zero]
    exact h.trans (Nat.cast_dvd_cast (hl.dvd_choose_pow h0 hN'))
end GlobalTheory
end

set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open scoped BigOperators
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  intro O _ _ _ ϖ _ σ _ l μ hl hϖl F e m₀ hlow hm₀ hoth
  classical
  set W := ∑ q, m₀ q * l ^ e q with hW
  set g : σ → Polynomial O := fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1 with hgdef
  set c : (σ →₀ ℕ) → O := fun m => (∏ q, g q ^ m q).coeff W with hc
  have hexp : (MvPolynomial.aeval g F).coeff W = ∑ m ∈ F.support, F.coeff m * c m := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hcong : ∀ m : σ →₀ ℕ, ϖ ∣ c m - if W = ∑ q, m q * l ^ e q then 1 else 0 := by
    intro m
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd ϖ g (fun q => l ^ e q)
      (fun q => by simpa [g] using C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow ϖ l (e q) hl hϖl) m) W
    simpa [Polynomial.coeff_X_pow] using h
  have hvanish : ∀ m : σ →₀ ℕ, W < m.degree → c m = 0 := by
    intro m hm
    have hX : ∀ q, Polynomial.X ∣ g q := fun q => by
      rw [Polynomial.X_dvd_iff]
      simp [g, Polynomial.coeff_one_add_X_pow]
    have hdvd : Polynomial.X ^ (∑ q, m q) ∣ ∏ q, g q ^ m q := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q _ => pow_dvd_pow_of_dvd (hX q) _
    rw [Finsupp.degree_eq_sum] at hm
    exact (Polynomial.X_pow_dvd_iff.1 hdvd) W hm
  have hdeg : ∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m q * l ^ e q := by
    intro m
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl.pos _)
  have hterm : ∀ m, m ≠ m₀ → ϖ ^ (μ + 1) ∣ F.coeff m * c m := by
    intro m hne
    by_cases hw : ∑ q, m q * l ^ e q ≤ W
    · exact dvd_mul_of_dvd_left (hoth m hne hw) _
    by_cases hd : m.degree ≤ W
    · have h1 := hcong m
      rw [if_neg (by omega), sub_zero] at h1
      rw [pow_succ]
      exact mul_dvd_mul (hlow m hd) h1
    · rw [hvanish m (by omega), mul_zero]
      exact dvd_zero _
  have hmain : ϖ ^ (μ + 1) ∣ F.coeff m₀ * c m₀ - F.coeff m₀ := by
    have h1 := hcong m₀
    rw [if_pos rfl] at h1
    rw [← mul_sub_one, pow_succ]
    exact mul_dvd_mul (hlow m₀ (hdeg m₀)) h1
  have hmem : m₀ ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    exact hm₀ (h0 ▸ dvd_zero _)
  intro hdiv
  rw [hexp, ← Finset.add_sum_erase _ _ hmem] at hdiv
  have hrest : ϖ ^ (μ + 1) ∣ ∑ m ∈ F.support.erase m₀, F.coeff m * c m :=
    Finset.dvd_sum fun m hm => hterm m (Finset.ne_of_mem_erase hm)
  have h2 := (dvd_add_left hrest).1 hdiv
  exact hm₀ (by simpa using dvd_sub h2 hmain)
end _root_.GlobalTheory
end GlobalTheory
