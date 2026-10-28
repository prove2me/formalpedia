-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:27.219363+00:00
-- url     : https://prove2.me/submissions/8c45916f-c6ec-4549-b300-70b406d63e5b

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Real clamped compensator integral.** For `0 ≤ t`,
`∫_{[0,t]} (G.eval u ω)² du = ∑ᵢ (min pᵢ₊₁ t − min pᵢ t)·ξᵢ²`. The real-Bochner
companion of `lintegral_eval_sq_clamped`, obtained from it by
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.toReal`. The simple-level
quadratic-variation compensator `A_t = ∫_{[0,t]} (eval)²` in closed sum form. -/
lemma solution {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by
  have h_len_nn : ∀ i : Fin G.N,
      0 ≤ min (G.partition i.succ) t - min (G.partition i.castSucc) t :=
    fun i => sub_nonneg.mpr (min_le_min_right t
      (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))
  have h_eval_meas : Measurable (fun u => G.eval u ω) :=
    G.eval_jointly_measurable.comp
      (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
        (h_eval_meas.pow_const 2).aestronglyMeasurable]
  rw [show (fun u => ENNReal.ofReal ((G.eval u ω) ^ 2))
        = fun u => (‖G.eval u ω‖₊ : ℝ≥0∞) ^ 2 from funext (fun u => (h_norm_sq _).symm),
    LevyStochCalc.Brownian.Ito.lintegral_eval_sq_clamped G ω,
    show (fun i : Fin G.N => ENNReal.ofReal (min (G.partition i.succ) t
          - min (G.partition i.castSucc) t) * (‖G.ξ i ω‖₊ : ℝ≥0∞) ^ 2)
        = fun i => ENNReal.ofReal ((min (G.partition i.succ) t
            - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2) from
      funext (fun i => by rw [h_norm_sq, ← ENNReal.ofReal_mul (h_len_nn i)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)),
    ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)))]
