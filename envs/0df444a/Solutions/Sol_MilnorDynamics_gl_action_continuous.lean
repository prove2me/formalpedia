-- Prove2me | solution 1 for MilnorDynamics.gl_action_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T09:14:46.618999+00:00
-- url     : https://prove2.me/submissions/37af5507-9c8a-46fc-8651-ba623440ea29

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint Topology
open Bornology
open Filter Set
open MilnorDynamics

/-- Inversion about a point tends to the cobounded filter. -/
private lemma poleInv_tendsto_cobounded (z₀ : ℂ) :
    Tendsto (fun x : ℂ => (x - z₀)⁻¹) (𝓝[≠] z₀) (cobounded ℂ) := by
  have hshift : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousWithinAt (fun z : ℂ => z - z₀) {z₀}ᶜ z₀ := by fun_prop
      simpa using hc.tendsto
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa [sub_eq_zero] using hy
  exact Filter.tendsto_inv₀_nhdsNE_zero.comp hshift

/-- The reciprocal of an affine function with a simple zero at `z₀` tends to the cobounded
filter. -/
private lemma poleInv_tendsto {r s z₀ : ℂ} (hpole : r * z₀ + s = 0) (hr : r ≠ 0) :
    Tendsto (fun z : ℂ => (r * z + s)⁻¹) (𝓝[≠] z₀) (cobounded ℂ) := by
  have hshift : Tendsto (fun z : ℂ => r * z + s) (𝓝[≠] z₀) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousWithinAt (fun z : ℂ => r * z + s) {z₀}ᶜ z₀ := by fun_prop
      simpa [hpole] using hc.tendsto
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro hzero
      have hzero' : r * y + s = 0 := hzero
      exact hy (mul_left_cancel₀ hr (by linear_combination hzero' - hpole))
  exact Filter.tendsto_inv₀_nhdsNE_zero.comp hshift

/-- A fractional linear function with a simple pole at `z₀` tends to the cobounded filter. -/
private lemma quotient_tendsto_cobounded {p q r s z₀ : ℂ} (hpole : r * z₀ + s = 0)
    (hr : r ≠ 0) (hnum : p * z₀ + q ≠ 0) :
    Tendsto (fun z : ℂ => (p * z + q) / (r * z + s)) (𝓝[≠] z₀) (cobounded ℂ) := by
  have hbase : Tendsto (fun z : ℂ => (r * z + s)⁻¹) (𝓝[≠] z₀) (cobounded ℂ) :=
    poleInv_tendsto hpole hr
  have hstep : Tendsto (fun z : ℂ => (p * z₀ + q) * (r * z + s)⁻¹ + p / r)
      (𝓝[≠] z₀) (cobounded ℂ) :=
    (tendsto_add_const_cobounded (p / r)).comp
      ((Filter.tendsto_mul_left_cobounded hnum).comp hbase)
  refine hstep.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z - z₀ ≠ 0 := fun h => hz (sub_eq_zero.mp h)
  have hden : r * z + s = r * (z - z₀) := by linear_combination hpole
  have hden0 : r * (z - z₀) ≠ 0 := mul_ne_zero hr hz0
  rw [hden]
  field_simp
  ring

/-- A non-constant affine map sends the cocompact filter to the cocompact filter. -/
private lemma affine_tendsto_cocompact {r s : ℂ} (hr : r ≠ 0) :
    Tendsto (fun z : ℂ => r * z + s) (cocompact ℂ) (cocompact ℂ) := by
  have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) ?_
  rw [Filter.tendsto_atTop]
  intro M
  filter_upwards [Filter.tendsto_atTop.mp (tendsto_dist_left_cocompact_atTop (0 : ℂ))
    ((M + ‖s‖) / ‖r‖)] with z hz
  have h1 : M + ‖s‖ ≤ ‖r‖ * ‖z‖ := by
    have := mul_le_mul_of_nonneg_left hz (le_of_lt hrpos)
    rwa [dist_comm, dist_zero_right, mul_div_cancel₀ _ (ne_of_gt hrpos)] at this
  have h2 : ‖r‖ * ‖z‖ - ‖s‖ ≤ ‖r * z + s‖ := by
    have h := norm_add_le (r * z + s) (-s)
    rw [add_neg_cancel_right, norm_neg, norm_mul] at h
    linarith
  rw [dist_zero_right]
  linarith

/-- Dividing a non-constant affine map by a nonzero constant still escapes. -/
private lemma div_const_tendsto_cocompact {p q s : ℂ} (hp : p ≠ 0) (hs : s ≠ 0) :
    Tendsto (fun z : ℂ => (p * z + q) / s) (cocompact ℂ) (cocompact ℂ) := by
  have hfun : (fun z : ℂ => (p * z + q) / s) = fun z => (p / s) * z + (q / s) := by
    funext z
    ring
  rw [hfun]
  exact affine_tendsto_cocompact (div_ne_zero hp hs)

/-- A fractional linear function tends to `p / r` along the cocompact filter. -/
private lemma quotient_tendsto_cocompact {p q r s : ℂ} (hr : r ≠ 0) :
    Tendsto (fun z : ℂ => (p * z + q) / (r * z + s)) (cocompact ℂ) (𝓝 (p / r)) := by
  have hden : Tendsto (fun z : ℂ => r * z + s) (cocompact ℂ) (cocompact ℂ) :=
    affine_tendsto_cocompact hr
  have hinv : Tendsto (fun z : ℂ => (r * z + s)⁻¹) (cocompact ℂ) (𝓝 0) :=
    Filter.tendsto_inv₀_cobounded.comp (hden.mono_right Metric.cobounded_eq_cocompact.ge)
  have hdiff : Tendsto (fun z : ℂ => (p * z + q) / (r * z + s) - p / r)
      (cocompact ℂ) (𝓝 0) := by
    have hfun : (fun z : ℂ => ((q * r - p * s) / r) * (r * z + s)⁻¹)
        =ᶠ[cocompact ℂ] fun z => (p * z + q) / (r * z + s) - p / r := by
      have hnorm : Tendsto (fun z : ℂ => ‖r * z + s‖) (cocompact ℂ) atTop :=
        tendsto_norm_atTop_iff_cobounded.mpr
          (hden.mono_right Metric.cobounded_eq_cocompact.ge)
      filter_upwards [hnorm.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
      have hz0 : r * z + s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz)
      field_simp
      ring
    simpa using (hinv.const_mul ((q * r - p * s) / r)).congr' hfun
  have := hdiff.add_const (p / r)
  simpa [sub_add_cancel] using this

theorem solution (g : GL (Fin 2) ℂ) :
    Continuous (fun x : OnePoint ℂ => g • x) ∧ Continuous (fun x : OnePoint ℂ => g⁻¹ • x) := by
  have key : ∀ h : GL (Fin 2) ℂ, Continuous (fun x : OnePoint ℂ => h • x) := by
    intro h
    have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by
      simpa [Matrix.det_fin_two] using h.det_ne_zero
    have hcoe_cocompact : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ)
        (𝓝 (∞ : OnePoint ℂ)) :=
      OnePoint.tendsto_coe_infty.mono_left (le_of_eq Filter.coclosedCompact_eq_cocompact.symm)
    have hcoe_cobounded : Tendsto ((↑) : ℂ → OnePoint ℂ) (cobounded ℂ)
        (𝓝 (∞ : OnePoint ℂ)) :=
      hcoe_cocompact.mono_left (le_of_eq Metric.cobounded_eq_cocompact)
    rw [OnePoint.continuous_iff]
    refine ⟨?_, ?_⟩
    · -- behaviour at `∞`
      by_cases hr : h 1 0 = 0
      · have hinf : h • (∞ : OnePoint ℂ) = ∞ := by
          rw [OnePoint.smul_infty_eq_ite, if_pos hr]
        rw [hinf]
        have hs : h 1 1 ≠ 0 := by
          intro hs
          exact hdet (by rw [hr, hs]; ring)
        have hp : h 0 0 ≠ 0 := by
          intro hp
          exact hdet (by rw [hr, hp]; ring)
        have hfun : (fun z : ℂ => h • (z : OnePoint ℂ))
            = fun z => (↑((h 0 0 * z + h 0 1) / h 1 1) : OnePoint ℂ) := by
          funext z
          rw [OnePoint.smul_some_eq_ite, if_neg]
          · rw [hr, zero_mul, zero_add]
          · rw [hr, zero_mul, zero_add]
            exact fun hz => hs hz
        rw [hfun, Filter.coclosedCompact_eq_cocompact]
        exact hcoe_cocompact.comp
          (div_const_tendsto_cocompact (p := h 0 0) (q := h 0 1) (s := h 1 1) hp hs)
      · have hinf : h • (∞ : OnePoint ℂ) = ((h 0 0 / h 1 0 : ℂ) : OnePoint ℂ) := by
          rw [OnePoint.smul_infty_eq_ite, if_neg hr]
        rw [hinf, Filter.coclosedCompact_eq_cocompact]
        have hev : (fun z : ℂ => h • (z : OnePoint ℂ)) =ᶠ[cocompact ℂ]
            fun z => (↑((h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1)) : OnePoint ℂ) := by
          have hden : Tendsto (fun z : ℂ => h 1 0 * z + h 1 1) (cocompact ℂ) (cocompact ℂ) :=
            affine_tendsto_cocompact (r := h 1 0) (s := h 1 1) hr
          have hnorm : Tendsto (fun z : ℂ => ‖h 1 0 * z + h 1 1‖) (cocompact ℂ) atTop :=
            tendsto_norm_atTop_iff_cobounded.mpr
              (hden.mono_right Metric.cobounded_eq_cocompact.ge)
          filter_upwards [hnorm.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
          rw [OnePoint.smul_some_eq_ite, if_neg]
          exact fun hzero => (norm_ne_zero_iff.mp (ne_of_gt hz)) hzero
        exact ((OnePoint.continuous_coe.tendsto (h 0 0 / h 1 0)).comp
          (quotient_tendsto_cocompact (p := h 0 0) (q := h 0 1) (r := h 1 0)
            (s := h 1 1) hr)).congr' hev.symm
    · -- continuity on `ℂ`
      rw [continuous_iff_continuousAt]
      intro z₀
      rw [continuousAt_iff_punctured_nhds]
      by_cases hpole : h 1 0 * z₀ + h 1 1 = 0
      · have hr : h 1 0 ≠ 0 := by
          intro hr
          have hs : h 1 1 = 0 := by simpa [hr] using hpole
          exact hdet (by rw [hr, hs]; ring)
        have hnum : h 0 0 * z₀ + h 0 1 ≠ 0 := by
          intro hn
          have h1 : h 0 1 = -(h 0 0 * z₀) := by linear_combination hn
          have h2 : h 1 1 = -(h 1 0 * z₀) := by linear_combination hpole
          exact hdet (by rw [h1, h2]; ring)
        have hev : (fun z : ℂ => h • (z : OnePoint ℂ)) =ᶠ[𝓝[≠] z₀]
            fun z => (↑((h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1)) : OnePoint ℂ) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          rw [OnePoint.smul_some_eq_ite, if_neg]
          intro hzero
          have h3 : h 1 0 * (z - z₀) = 0 := by linear_combination hzero - hpole
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hr h4
          · exact hz (sub_eq_zero.mp h4)
        rw [show h • (z₀ : OnePoint ℂ) = (∞ : OnePoint ℂ) from by
              rw [OnePoint.smul_some_eq_ite, if_pos hpole]]
        exact (hcoe_cobounded.comp (quotient_tendsto_cobounded hpole hr hnum)).congr' hev.symm
      · have hcont : Tendsto (fun z : ℂ => (h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1))
            (𝓝 z₀) (𝓝 ((h 0 0 * z₀ + h 0 1) / (h 1 0 * z₀ + h 1 1))) :=
          (((continuous_const.mul continuous_id).add continuous_const).continuousAt).div
            (((continuous_const.mul continuous_id).add continuous_const).continuousAt) hpole
        have hev : (fun z : ℂ => h • (z : OnePoint ℂ)) =ᶠ[𝓝[≠] z₀]
            fun z => (↑((h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1)) : OnePoint ℂ) := by
          have hcw : ContinuousWithinAt (fun z : ℂ => h 1 0 * z + h 1 1) {z₀}ᶜ z₀ := by
            fun_prop
          filter_upwards [hcw.eventually (isOpen_compl_singleton.mem_nhds hpole)] with z hz
          rw [OnePoint.smul_some_eq_ite, if_neg (by simpa using hz)]
        rw [show h • (z₀ : OnePoint ℂ)
              = ((↑((h 0 0 * z₀ + h 0 1) / (h 1 0 * z₀ + h 1 1)) : OnePoint ℂ)) from by
            rw [OnePoint.smul_some_eq_ite, if_neg hpole]]
        exact ((OnePoint.continuous_coe.tendsto
          ((h 0 0 * z₀ + h 0 1) / (h 1 0 * z₀ + h 1 1))).comp
          (hcont.mono_left nhdsWithin_le_nhds)).congr' hev.symm
  exact ⟨key g, key g⁻¹⟩
