-- Prove2me | solution 1 for MultiStoreAssort.Pricing.single_store_optimum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:28:48.181995+00:00
-- url     : https://prove2.me/submissions/c6a7a381-355e-4723-9282-15dde65d17ea

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

set_option autoImplicit false
open Finset MultiStoreAssort.Pricing

lemma yb_key (a b p θ : ℝ) (hb : 0 < b) :
    (p - θ) * Real.exp (a - b * p) ≤ Real.exp ((a - Real.log b - 1) - b * θ) := by
  have e : (a - Real.log b - 1) - b * θ = (a - b * p) + (b * (p - θ) - 1) + (-Real.log b) := by ring
  rw [e, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hb]
  have h1 : b * (p - θ) ≤ Real.exp (b * (p - θ) - 1) := by
    have := Real.add_one_le_exp (b * (p - θ) - 1); linarith
  have hE : 0 < Real.exp (a - b * p) := Real.exp_pos _
  have h2 : Real.exp (a - b * p) * (b * (p - θ)) * b⁻¹ = (p - θ) * Real.exp (a - b * p) := by
    field_simp
  calc (p - θ) * Real.exp (a - b * p) = Real.exp (a - b * p) * (b * (p - θ)) * b⁻¹ := h2.symm
    _ ≤ Real.exp (a - b * p) * Real.exp (b * (p - θ) - 1) * b⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb.le)
        exact mul_le_mul_of_nonneg_left h1 hE.le

theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (θ : ℝ) (hθ : IsTheta a b θ) :
    (∀ (S : Finset (Fin n)) (p : Fin n → ℝ), rev14 a b S p ≤ θ) ∧
      rev14 a b Finset.univ (fun k => θ + 1 / b k) = θ := by
  have hθ' : θ = ∑ k, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) := hθ
  have hpos : ∀ (S : Finset (Fin n)) (p : Fin n → ℝ),
      0 < 1 + ∑ k ∈ S, Real.exp (a k - b k * p k) := by
    intro S p
    have : 0 ≤ ∑ k ∈ S, Real.exp (a k - b k * p k) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    linarith
  refine ⟨fun S p => ?_, ?_⟩
  · unfold rev14
    rw [div_le_iff₀ (hpos S p)]
    have h1 : ∑ k ∈ S, (p k - θ) * Real.exp (a k - b k * p k) ≤
        ∑ k ∈ S, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) :=
      Finset.sum_le_sum fun k _ => yb_key (a k) (b k) (p k) θ (hb k)
    have h2 : ∑ k ∈ S, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) ≤
        ∑ k, Real.exp ((a k - Real.log (b k) - 1) - b k * θ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun k _ _ => (Real.exp_pos _).le)
    have h3 : ∑ k ∈ S, (p k - θ) * Real.exp (a k - b k * p k) =
        ∑ k ∈ S, p k * Real.exp (a k - b k * p k) - θ * ∑ k ∈ S, Real.exp (a k - b k * p k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    nlinarith
  · unfold rev14
    rw [div_eq_iff (hpos _ _).ne']
    have h3 : ∀ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) =
        Real.exp ((a k - Real.log (b k) - 1) - b k * θ) := by
      intro k
      have hbk := hb k
      have e : (a k - Real.log (b k) - 1) - b k * θ =
          (a k - b k * (θ + 1 / b k)) + (-Real.log (b k)) := by
        have : b k * (1 / b k) = 1 := by field_simp
        rw [mul_add, this]; ring
      rw [e, Real.exp_add, Real.exp_neg, Real.exp_log hbk]
      field_simp
      ring
    have h4 : ∑ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) = θ := by
      exact (Finset.sum_congr rfl fun k _ => h3 k).trans hθ'.symm
    have h5 : ∑ k, (θ + 1 / b k - θ) * Real.exp (a k - b k * (θ + 1 / b k)) =
        ∑ k, (θ + 1 / b k) * Real.exp (a k - b k * (θ + 1 / b k)) -
          θ * ∑ k, Real.exp (a k - b k * (θ + 1 / b k)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith
