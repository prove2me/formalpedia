-- Prove2me | solution 1 for NonmonotoneLS.RLinear.step_segment_mem_Lbar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T22:16:58.957094+00:00
-- url     : https://prove2.me/submissions/d5ff4295-42ef-4440-b141-9046773379ea

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter
open NonmonotoneLS.RLinear

theorem solution {n : ℕ} (p : NonmonotoneLS.Shared.Params)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) (s t : ℝ)
    (hx : x k ∈ levelSet f (x 0))
    (hs0 : 0 ≤ s) (hsμ : s ≤ p.μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x k + t • (s • d k) ∈ Lbar p f x d := by
  change Metric.infEDist (x k + t • (s • d k)) (levelSet f (x 0)) ≤
    ENNReal.ofReal p.μ * dmax d
  have hcal : ‖t • (s • d k)‖ = t * s * ‖d k‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ht0, abs_of_nonneg hs0]
    ring
  have hmem : edist (x k + t • (s • d k)) (x k) = ENNReal.ofReal (t * s * ‖d k‖) := by
    rw [edist_dist, dist_eq_norm, add_sub_cancel_left, hcal]
  have hdmax : ‖d k‖ₑ ≤ dmax d := by
    unfold dmax
    simpa only [enorm_eq_nnnorm] using
      (le_iSup (fun j : ℕ => (‖d j‖₊ : ENNReal)) k)
  calc
    Metric.infEDist (x k + t • (s • d k)) (levelSet f (x 0))
        ≤ edist (x k + t • (s • d k)) (x k) := Metric.infEDist_le_edist_of_mem hx
    _ = ENNReal.ofReal (t * s * ‖d k‖) := hmem
    _ ≤ ENNReal.ofReal (p.μ * ‖d k‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hts : t * s ≤ p.μ := by nlinarith [mul_nonneg ht0 hs0, mul_le_mul ht1 hsμ]
        exact mul_le_mul_of_nonneg_right hts (norm_nonneg _)
    _ = ENNReal.ofReal p.μ * ‖d k‖ₑ := by
      rw [ENNReal.ofReal_mul p.μ_pos.le, ofReal_norm]
    _ ≤ ENNReal.ofReal p.μ * dmax d :=
          mul_le_mul_right hdmax (ENNReal.ofReal p.μ)
