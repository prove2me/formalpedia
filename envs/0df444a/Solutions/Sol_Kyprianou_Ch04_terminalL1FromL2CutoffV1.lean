-- Prove2me | solution 1 for Kyprianou.Ch04.terminalL1FromL2CutoffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:08.9772+00:00
-- url     : https://prove2.me/submissions/af4ff397-f9d4-4f6e-932f-1f4ee30b5946

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal
set_option autoImplicit false

/-- L2 convergence on a probability space implies L1 convergence of the same sequence. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hm : ∀ n, Measurable (Y n)) (hM : Measurable M)
    (hi : ∀ n, Integrable (fun w => (Y n w)^2) P)
    (hI : Integrable (fun w => (M w)^2) P)
    (h : Tendsto (fun n => ∫ w, (Y n w - M w)^2 ∂P) atTop (𝓝 0)) :
    Integrable M P ∧ Tendsto (fun n => ∫ w, |Y n w - M w| ∂P) atTop (𝓝 0) := by
  have hMp := (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mpr hI
  refine ⟨hMp.integrable (by norm_num),?_⟩
  have hD (n : ℕ) : Integrable (fun w => |Y n w - M w|) P :=
    (((memLp_two_iff_integrable_sq (hm n).aestronglyMeasurable).mpr (hi n)).sub hMp).integrable
      (by norm_num) |>.abs
  apply Metric.tendsto_nhds.mpr
  intro δ hd
  filter_upwards [Metric.tendsto_nhds.mp h (δ^2/2) (by positivity)] with n hn
  have he (w : Ω) : |Y n w - M w| ≤
      (Y n w - M w)^2 / δ + δ/4 := by
    have hp := sq_nonneg (|Y n w - M w| - δ/2)
    have hh : |Y n w - M w|^2 = (Y n w - M w)^2 := sq_abs _
    have hle : |Y n w - M w| * δ ≤ (Y n w - M w)^2 + δ/4*δ := by nlinarith
    calc
      _ ≤ ((Y n w - M w)^2 + δ/4*δ)/δ := (le_div_iff₀ hd).mpr hle
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hd.ne']
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have hSq := (((memLp_two_iff_integrable_sq (hm n).aestronglyMeasurable).mpr
    (hi n)).sub hMp).integrable_sq
  have hB := integral_mono (hD n) ((hSq.div_const δ).add (integrable_const (δ/4))) he
  change (∫ w, |Y n w - M w| ∂P) ≤
    ∫ w, (Y n w - M w)^2 / δ + δ/4 ∂P at hB
  have hSq' : Integrable (fun w => (Y n w - M w)^2) P := hSq
  rw [integral_add (hSq'.div_const δ) (integrable_const _),integral_div,integral_const] at hB
  simp [measureReal_def] at hB
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hn
  apply hB.trans_lt
  have hlt : (∫ w, (Y n w - M w)^2 ∂P) / δ < δ/2 :=
    (div_lt_iff₀ hd).mpr (by nlinarith)
  linarith
