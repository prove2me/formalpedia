-- Prove2me | solution 1 for MultiStoreAssort.Pricing.theta_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:08:49.763505+00:00
-- url     : https://prove2.me/submissions/c345ea9f-351b-4f1b-b2d7-b8ab8c0f2b52

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

set_option autoImplicit false
open Finset MultiStoreAssort.Pricing

theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) :
    ∃! θ : ℝ, IsTheta a b θ := by
  set c : Fin n → ℝ := fun k => a k - Real.log (b k) - 1 with hc
  let F : ℝ → ℝ := fun θ => θ - ∑ k, Real.exp (c k - b k * θ)
  have hFcont : Continuous F := by
    apply Continuous.sub continuous_id
    apply continuous_finset_sum
    intro k _
    exact Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hFmono : StrictMono F := by
    intro x y hxy
    have h1 : ∑ k, Real.exp (c k - b k * y) ≤ ∑ k, Real.exp (c k - b k * x) := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.exp_le_exp.2
      have := hb k
      nlinarith
    show x - ∑ k, Real.exp (c k - b k * x) < y - ∑ k, Real.exp (c k - b k * y)
    linarith
  have hroot : ∀ θ, IsTheta a b θ ↔ F θ = 0 := by
    intro θ
    simp only [IsTheta, F, hc]
    constructor <;> intro h <;> linarith
  have hlow : F (-1) < 0 := by
    have : 0 ≤ ∑ k, Real.exp (c k - b k * (-1)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    show (-1 : ℝ) - ∑ k, Real.exp (c k - b k * (-1)) < 0
    linarith
  set C : ℝ := ∑ k, Real.exp (c k) with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  have hup : 0 < F (C + 1) := by
    have : ∑ k, Real.exp (c k - b k * (C + 1)) ≤ C := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.exp_le_exp.2
      have := hb k
      nlinarith
    show 0 < (C + 1) - ∑ k, Real.exp (c k - b k * (C + 1))
    linarith
  have hle : (-1 : ℝ) ≤ C + 1 := by linarith
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc hle hFcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F (-1)) (F (C + 1)) from ⟨hlow.le, hup.le⟩)
  refine ⟨θ, (hroot θ).2 hθ, fun θ' hθ' => ?_⟩
  exact hFmono.injective (((hroot θ').1 hθ').trans hθ.symm)
