-- Prove2me | solution 1 for Kyprianou.Ch04.fullCutoffTerminalL2ClosureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:53:58.159183+00:00
-- url     : https://prove2.me/submissions/da9293a4-14d5-4392-960a-585d333faef0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_square_lintegral_fatou_integrable
open MeasureTheory Filter Set Topology
open scoped ENNReal
set_option autoImplicit false

/-- A terminal square Cauchy family converges in square mean to its subsequential almost-sure limit. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → ℝ) (M : Ω → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n ∧ e n < 1) (he0 : Tendsto e atTop (𝓝 0))
    (hm : ∀ a, 0 < a → a < 1 → Measurable (Y a))
    (hi : ∀ a, 0 < a → a < 1 → Integrable (fun w => (Y a w)^2) P)
    (hM : Measurable M)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => Y (e n) w) atTop (𝓝 (M w)))
    (hc : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∫ w, (Y a w - Y b w)^2 ∂P) ≤ δ) :
    Integrable (fun w => (M w)^2) P ∧
      Tendsto (fun a => ∫ w, (Y a w - M w)^2 ∂P) (𝓝[>] 0) (𝓝 0) := by
  have hbound (δ : ℝ) (hd : 0 < δ) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ a, 0 < a → a < r → Integrable (fun w => (Y a w - M w)^2) P ∧
        (∫ w, (Y a w - M w)^2 ∂P) ≤ δ := by
    obtain ⟨r,hr,hr1,hc'⟩ := hc δ hd
    refine ⟨r,hr,hr1,?_⟩
    intro a ha har
    have hmeas (n : ℕ) := (hm a ha (har.trans hr1)).sub (hm (e n) (he n).1 (he n).2)
    have hint (n : ℕ) : Integrable (fun w => (Y a w - Y (e n) w)^2) P :=
      (((memLp_two_iff_integrable_sq (hm a ha (har.trans hr1)).aestronglyMeasurable).mpr
        (hi a ha (har.trans hr1))).sub
        ((memLp_two_iff_integrable_sq (hm (e n) (he n).1 (he n).2).aestronglyMeasurable).mpr
        (hi (e n) (he n).1 (he n).2))).integrable_sq
    have hlim' : ∀ᵐ w ∂P, Tendsto (fun n => Y a w - Y (e n) w) atTop (𝓝 (Y a w - M w)) :=
      hlim.mono fun w hw => tendsto_const_nhds.sub hw
    have hB : ∀ᶠ n : ℕ in atTop,
        (∫⁻ w, ENNReal.ofReal ((Y a w - Y (e n) w)^2) ∂P) ≤ ENNReal.ofReal δ := by
      filter_upwards [(tendsto_order.mp he0).2 r hr] with n hn
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun w => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hc' a (e n) ha har (he n).1 hn)
    obtain ⟨hI,hB'⟩ :=
      AvramDividend.Classical.avram_p2_j_ui_real_square_lintegral_fatou_integrable P
        (fun n w => Y a w - Y (e n) w) (fun w => Y a w - M w)
        (ENNReal.ofReal δ) ENNReal.ofReal_ne_top hmeas
        ((hm a ha (har.trans hr1)).sub hM).aestronglyMeasurable hlim' hB
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun w => sq_nonneg _)] at hB'
    exact ⟨hI,(ENNReal.ofReal_le_ofReal_iff hd.le).mp hB'⟩
  obtain ⟨r,hr,hr1,h⟩ := hbound 1 zero_lt_one
  have ha : 0 < r/2 := by positivity
  have har : r/2 < r := by linarith
  have hD := (h _ ha har).1
  have hY := (memLp_two_iff_integrable_sq (hm _ ha (har.trans hr1)).aestronglyMeasurable).mpr
    (hi _ ha (har.trans hr1))
  have hDM := (memLp_two_iff_integrable_sq
    ((hm _ ha (har.trans hr1)).sub hM).aestronglyMeasurable).mpr hD
  have hEq : M = Y (r/2) - (Y (r/2) - M) := by abel
  refine ⟨hEq ▸ (hY.sub hDM).integrable_sq,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro δ hd
  obtain ⟨a,ha,ha1,hA⟩ := hbound (δ/2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT ha] with b hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun w => sq_nonneg _)]
  exact (hA b hb.1 hb.2).2.trans_lt (by linarith)
