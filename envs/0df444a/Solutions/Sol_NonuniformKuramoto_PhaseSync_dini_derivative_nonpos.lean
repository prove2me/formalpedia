-- Prove2me | solution 1 for NonuniformKuramoto.PhaseSync.dini_derivative_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:44:21.471987+00:00
-- url     : https://prove2.me/submissions/0f45b5f0-76be-4de0-8581-6e0bcd9a94a3

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model


theorem solution {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi) (θ : Fin n → ℝ) (hθ : NonuniformKuramoto.CondI.ArcClosed γ θ)
    (m ℓ : Fin n) (hm : ∀ k, θ k ≤ θ m) (hℓ : ∀ k, θ ℓ ≤ θ k) :
    NonuniformKuramoto.CondI.field D ω P ϕ θ m - NonuniformKuramoto.CondI.field D ω P ϕ θ ℓ
        = -∑ k, (P m k / D m * Real.sin (θ m - θ k) + P ℓ k / D ℓ * Real.sin (θ k - θ ℓ)) ∧
      NonuniformKuramoto.CondI.field D ω P ϕ θ m - NonuniformKuramoto.CondI.field D ω P ϕ θ ℓ ≤ 0 := by
  have hP' : ∀ i j, 0 ≤ P i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hPii]
    · exact hP i j h
  have hfield : ∀ i, NonuniformKuramoto.CondI.field D ω P ϕ θ i
      = ωbar - ∑ k, P i k / D i * Real.sin (θ i - θ k) := by
    intro i
    unfold NonuniformKuramoto.CondI.field
    simp only [hϕ, add_zero]
    rw [← hω i, sub_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hid : NonuniformKuramoto.CondI.field D ω P ϕ θ m - NonuniformKuramoto.CondI.field D ω P ϕ θ ℓ
        = -∑ k, (P m k / D m * Real.sin (θ m - θ k) + P ℓ k / D ℓ * Real.sin (θ k - θ ℓ)) := by
    rw [hfield, hfield, Finset.sum_add_distrib, sub_sub_sub_cancel_left, neg_add, sub_eq_add_neg]
    rw [add_comm]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show θ k - θ ℓ = -(θ ℓ - θ k) by ring, Real.sin_neg]
    ring
  refine ⟨hid, ?_⟩
  rw [hid, neg_nonpos]
  refine Finset.sum_nonneg (fun k _ => ?_)
  have hs1 : 0 ≤ Real.sin (θ m - θ k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hm k]) (by linarith [hθ m k])
  have hs2 : 0 ≤ Real.sin (θ k - θ ℓ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hℓ k]) (by linarith [hθ k ℓ])
  have a1 : 0 ≤ P m k / D m := div_nonneg (hP' m k) (hD m).le
  have a2 : 0 ≤ P ℓ k / D ℓ := div_nonneg (hP' ℓ k) (hD ℓ).le
  positivity
