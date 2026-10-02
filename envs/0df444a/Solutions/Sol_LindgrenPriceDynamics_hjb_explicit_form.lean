-- Prove2me | solution 1 for LindgrenPriceDynamics.hjb_explicit_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:37:57.518874+00:00
-- url     : https://prove2.me/submissions/b3f95c90-9137-4fb8-a30c-46cd1d734e26

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
lemma hjb76_ham_eq {l : ℕ} (m E : ℝ) (hm : 0 < m) (g v : Fin l → ℝ) :
    hamiltonian m E g v = (E - dot g g / (2 * m)) + ∑ i, m / 2 * (v i + g i / m) ^ 2 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have h : ∀ i, m / 2 * (v i + g i / m) ^ 2
      = 1 / 2 * m * (v i * v i) + g i * v i + g i * g i / (2 * m) := by
    intro i; field_simp; ring
  simp_rw [h]
  unfold hamiltonian dot
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  ring

open LindgrenPriceDynamics in
lemma hjb76_iInf {l : ℕ} (m E : ℝ) (hm : 0 < m) (g : Fin l → ℝ) :
    ⨅ v : Fin l → ℝ, hamiltonian m E g v = E - dot g g / (2 * m) := by
  apply ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · intro v
    rw [hjb76_ham_eq m E hm g v]
    have : 0 ≤ ∑ i, m / 2 * (v i + g i / m) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by linarith) (sq_nonneg _))
    linarith
  · intro w hw
    refine ⟨fun i => -(g i / m), ?_⟩
    rw [hjb76_ham_eq m E hm g]
    simp
    exact hw

open LindgrenPriceDynamics in
theorem solution {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hHJB : ∀ t p, -timePartial J t p =
      ⨅ v : Fin l → ℝ, hamiltonian m (aggregateExpenditure lam e p) (priceGrad (J t) p) v) :
    ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p := by
  intro t p
  have h := hHJB t p
  rw [hjb76_iInf m _ hm] at h
  linarith
