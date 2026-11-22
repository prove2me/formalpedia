-- Prove2me | solution 1 for MasulloRH.involutive_tsum_neg
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:55:23.889662+00:00
-- url     : https://prove2.me/submissions/21af44df-65c1-41cf-94cf-4350aa5fed10

import Mathlib
set_option autoImplicit false

theorem solution {ι : Type*} (σ : ι ≃ ι) (f : ι → ℂ)
    (hodd : ∀ i, f (σ i) = - f i) :
    ∑' i, f i = 0 := by
  have hσ : (∑' i, f i) = ∑' i, f (σ i) := (σ.tsum_eq f).symm
  have hrewrite : (∑' i, f (σ i)) = ∑' i, -f i := by
    apply tsum_congr
    intro i
    exact hodd i
  have hnegtsum : (∑' i, -f i) = -∑' i, f i := tsum_neg
  have h : (∑' i, f i) = -∑' i, f i := by
    calc
      (∑' i, f i) = ∑' i, f (σ i) := hσ
      _ = ∑' i, -f i := hrewrite
      _ = -∑' i, f i := hnegtsum
  have h2 : (∑' i, f i) + (∑' i, f i) = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  exact add_self_eq_zero.mp h2
