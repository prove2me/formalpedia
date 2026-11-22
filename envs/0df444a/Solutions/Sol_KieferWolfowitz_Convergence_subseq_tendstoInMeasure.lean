-- Prove2me | solution 1 for KieferWolfowitz.Convergence.subseq_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:59:06.535382+00:00
-- url     : https://prove2.me/submissions/703894fc-1d53-4aaf-8857-e2ed3e5b5181

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology KieferWolfowitz.Convergence

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ℝ → ℝ) (θ : ℝ) (h3 : Cond3 M θ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hc0 : Tendsto c atTop (𝓝 0))
    (z : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hint : ∀ j, Integrable (fun ω => K M c z (φ j) ω * |z (φ j) ω - θ|) P)
    (hlim : Tendsto (fun j => ∫ ω, K M c z (φ j) ω * |z (φ j) ω - θ| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun j => z (φ j)) atTop (fun _ => θ) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  -- Condition 3 at `δ/2` gives a uniform lower bound `π` for `K` away from `θ`.
  obtain ⟨π, hπ, hπK⟩ := h3 (δ / 2) (by positivity)
  have hδπ : 0 < π * δ := mul_pos hπ hδ
  -- Eventually `c (φ j) < δ/4`.
  have hcev : ∀ᶠ j in atTop, c (φ j) < δ / 4 :=
    (hc0.comp hφ.tendsto_atTop).eventually (gt_mem_nhds (by positivity))
  -- On `{δ ≤ |z - θ|}` we then have `π δ ≤ K |z - θ|`.
  have hsub : ∀ᶠ j in atTop, {ω | δ ≤ dist (z (φ j) ω) θ} ⊆
      {ω | π * δ ≤ K M c z (φ j) ω * |z (φ j) ω - θ|} := by
    filter_upwards [hcev] with j hj
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
    have hcj := hc (φ j)
    have hK : π < K M c z (φ j) ω := by
      have := hπK (z (φ j) ω) (by linarith) (c (φ j)) hcj (by linarith)
      rw [K, abs_div, abs_of_pos hcj]
      exact this
    calc π * δ ≤ π * |z (φ j) ω - θ| := mul_le_mul_of_nonneg_left hω hπ.le
      _ ≤ K M c z (φ j) ω * |z (φ j) ω - θ| :=
        mul_le_mul_of_nonneg_right hK.le (abs_nonneg _)
  -- Markov's inequality.
  have hbound : ∀ᶠ j in atTop, P.real {ω | δ ≤ dist (z (φ j) ω) θ} ≤
      (∫ ω, K M c z (φ j) ω * |z (φ j) ω - θ| ∂P) / (π * δ) := by
    filter_upwards [hsub] with j hj
    have hnn : 0 ≤ᵐ[P] fun ω => K M c z (φ j) ω * |z (φ j) ω - θ| :=
      Eventually.of_forall fun ω => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn (hint j) (π * δ)
    rw [le_div_iff₀ hδπ, mul_comm]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hj) hδπ.le).trans hmarkov
  have hupper : Tendsto (fun j => (∫ ω, K M c z (φ j) ω * |z (φ j) ω - θ| ∂P) / (π * δ))
      atTop (𝓝 0) := by
    simpa using hlim.div_const (π * δ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun j => measureReal_nonneg) hbound
