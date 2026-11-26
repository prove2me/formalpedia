-- Prove2me | solution 1 for LogLogJam.transcript_fisher_copy_cap
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:08.812257+00:00
-- url     : https://prove2.me/submissions/22d18dda-e32c-4f18-a601-3db3a4fd3f1f

import Theorems.Thm_LogLogJam_corollary_5_7
import Theorems.Thm_LogLogJam_seed_fisher_pointwise
import Theorems.Thm_LogLogJam_expected_batch_budget

open LogLogJam MeasureTheory
open scoped ENNReal

private theorem hist_mono {lam θ : ℝ} {T : ℕ} (P : GaussProtocol T) (t : ℕ)
    {F G : Hist t → ℝ≥0∞} (h : ∀ H, F H ≤ G H) :
    histInt lam θ P t F ≤ histInt lam θ P t G := by
  induction t with
  | zero => exact h _
  | succ t ih =>
    apply ih
    intro H
    apply lintegral_mono
    intro s
    apply lintegral_mono
    intro y
    exact mul_le_mul_right (h _) _

private theorem hist_smul {lam θ : ℝ} {T : ℕ} (P : GaussProtocol T) (t : ℕ)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) (F : Hist t → ℝ≥0∞) :
    histInt lam θ P t (fun H => r * F H) = r * histInt lam θ P t F := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [histInt, mul_left_comm _ r, lintegral_const_mul' r _ hr, ih]

theorem solution (lam : ℝ) (hlam : 1 < lam) {T : ℕ} (P : GaussProtocol T)
    (S : ℕ) (hS : CopiesLe lam P S) :
    Jbar lam P T ≤ ENNReal.ofReal ((4 * energy lam)^2 * (S : ℝ)) := by
  let A := ENNReal.ofReal ((4 * energy lam)^2)
  have hA : A ≠ ⊤ := ENNReal.ofReal_ne_top
  let m (t : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1/Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
    histInt lam θ P t (fun H => ∫⁻ s, (s.1 : ℝ≥0∞) ∂(P.seed t H))
  have hstep (t : ℕ) (ht : t+1 ≤ T) : Jbar lam P (t+1) ≤ Jbar lam P t + A * m t := by
    rw [corollary_5_7 P lam hlam t ht]
    apply add_le_add_right
    dsimp only [m]
    rw [mul_left_comm A, ← lintegral_const_mul' A _ hA]
    gcongr with θ
    rw [← hist_smul P t A hA]
    apply hist_mono
    intro H
    rw [← lintegral_const_mul' A _ hA]
    apply lintegral_mono_ae
    filter_upwards [P.seed_cov t H] with s hs
    exact seed_fisher_pointwise lam θ hlam s.1 s.2 hs
  have hsum (t : ℕ) (ht : t ≤ T) : Jbar lam P t ≤ A * ∑ i ∈ Finset.range t, m i := by
    induction t with
    | zero =>
      simp [Jbar, protoFisher, histInt, histDens]
    | succ t ih =>
      calc
        _ ≤ Jbar lam P t + A * m t := hstep t ht
        _ ≤ A * (∑ i ∈ Finset.range t, m i) + A * m t := by gcongr; exact ih (by omega)
        _ = _ := by rw [Finset.sum_range_succ, mul_add]
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_natCast]
  exact (hsum T le_rfl).trans (by gcongr; exact expected_batch_budget lam hlam P S hS)
