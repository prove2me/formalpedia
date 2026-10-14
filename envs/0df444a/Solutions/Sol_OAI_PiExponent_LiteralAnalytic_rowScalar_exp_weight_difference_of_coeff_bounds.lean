-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_coeff_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:57:12.244989+00:00
-- url     : https://prove2.me/submissions/1707e988-8441-426f-bd3d-5a0bfb361856
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_product_coeff_exp_bound_of_coordinate_coeff_bounds

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i))
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1)
    (hτs : ∀ i n, n < T i → PowerSeries.coeff n (τ i) = 0) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  have hprod := OAI.PiExponent.LiteralAnalytic.product_coeff_exp_bound_of_coordinate_coeff_bounds
    τ a β e k w H ws v hws hv hw ha hk hτc
  exact OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound
    ε τ β a e k w C ν H ws v F hC hν hws hv hF hw ha hk T hT hTw hτs hε hprod
