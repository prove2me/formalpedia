-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_controls
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:51:35.302523+00:00
-- url     : https://prove2.me/submissions/22eac41f-602a-4a63-88e8-4d76a4f744a0

import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_product_coeff_bound
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_product_weight_bound

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (H v F : ℝ) (hv : 0 < v) (hF : 0 < F) (hT : ∀ i, 1 ≤ T i)
    (hk : (k : ℝ) ≤ H / v)
    (hTw : ∀ i, F * w i ≤ v * T i) :
    ‖PowerSeries.coeff k
        (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ ((d i).val : ℕ))‖ ≤ (2 : ℝ) ^ k ∧
      (PowerSeries.coeff k
          (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ ((d i).val : ℕ)) ≠ 0 →
        weight w (fun i => (d i).val) ≤ H / F) := by
  constructor
  · exact OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_bound
      T β a d k
  · exact OAI.PiExponent.MatrixTranslationBounds.logTail_product_weight_bound
      T β a d k w H v F hv hF hT hk hTw