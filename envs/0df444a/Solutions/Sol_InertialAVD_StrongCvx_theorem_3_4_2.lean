-- Prove2me | solution 2 for InertialAVD.StrongCvx.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:20.251723+00:00
-- url     : https://prove2.me/submissions/534a84c1-09d3-4b25-8d8d-17f0430b7c51

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting
import Theorems.Thm_InertialAVD_StrongCvx_eq_26
import Theorems.Thm_InertialAVD_StrongCvx_eq_28
import Theorems.Thm_InertialAVD_StrongCvx_thm_3_4_last_display

-- carved verbatim out of submission 768e0991-d148-45e4-839a-fe02e7d7ec2e, lines 504-556

section
set_option autoImplicit false
open InnerProductSpace Filter Topology Asymptotics
open InertialAVD.StrongCvx

theorem avd_params (α : ℝ) (hα : 3 < α) :
    0 < pExp α ∧ 0 < lam α ∧ pExp α + 2 - lam α = 0 ∧ α - lam α - 1 - pExp α / 2 = 0 ∧
      α - lam α - 1 - pExp α = - pExp α / 2 := by
  unfold pExp lam
  refine ⟨by linarith, by linarith, by ring, by ring, by ring⟩

theorem avd_t1 (t₀ α μ : ℝ) (hα : 3 < α) (hμ : 0 < μ) (ht0 : 0 < t₀) (t : ℝ) (ht : t1 t₀ α μ ≤ t) :
    t₀ ≤ t ∧ 0 < t ∧ pExp α * lam α ≤ μ * t ^ 2 := by
  obtain ⟨hp, hl, -, -, -⟩ := avd_params α hα
  have h1 : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have h2 : 0 < t := lt_of_lt_of_le ht0 h1
  have h3 : Real.sqrt (pExp α * lam α / μ) ≤ t := le_trans (le_max_right _ _) ht
  have h4 : pExp α * lam α / μ ≤ t ^ 2 := by
    have := Real.sq_sqrt (show 0 ≤ pExp α * lam α / μ from by positivity)
    rw [← this]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  refine ⟨h1, h2, ?_⟩
  rw [div_le_iff₀ hμ] at h4
  linarith

theorem avd_gradzero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) : gradient Φ xstar = 0 := by
  have h0 : fderiv ℝ Φ xstar = 0 :=
    ((isMinOn_univ_iff.mpr hmin).isLocalMin Filter.univ_mem).fderiv_eq_zero
  simp [gradient, h0]

theorem avd_dist {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ) (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y)
    (y : H) : ‖y - xstar‖ ^ 2 ≤ 2 / μ * (Φ y - Φ xstar) := by
  have h := hsc.2 xstar y
  rw [avd_gradzero Φ xstar hmin] at h
  simp only [inner_zero_left, add_zero] at h
  have hμ := hsc.1
  have : ‖xstar - y‖ = ‖y - xstar‖ := norm_sub_rev _ _
  rw [this] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith

theorem avd_basic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (t : ℝ) (ht : t1 t₀ α μ ≤ t) :
    0 < t ∧ 0 ≤ Φ (x t) - Φ xstar ∧
    t ^ pExp α * t ^ 2 * (Φ (x t) - Φ xstar) ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) ∧
    energyP Φ x v xstar (lam α) (pExp α) t ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) := by
  obtain ⟨hp, hl, -, -, -⟩ := avd_params α hα
  have hμ := hsc.1
  obtain ⟨-, htp, hmu⟩ := avd_t1 t₀ α μ hα hμ hsol.1 t ht
  have h26 := (InertialAVD.StrongCvx.eq_26 Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht)
  have hN : 0 ≤ Φ (x t) - Φ xstar := by linarith [hmin (x t)]
  have hT : 0 ≤ t ^ pExp α := (Real.rpow_pos_of_pos htp _).le
  have hEge : t ^ pExp α * t ^ 2 * (Φ (x t) - Φ xstar) ≤ energyP Φ x v xstar (lam α) (pExp α) t := by
    unfold energyP energy
    have h0 : 0 ≤ 1 / 2 * ‖lam α • (x t - xstar) + t • v t‖ ^ 2 + 0 / 2 * ‖x t - xstar‖ ^ 2 := by positivity
    nlinarith [mul_nonneg hT h0]
  have hcoef : lam α * pExp α / (2 * μ) ≤ t ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hTN : 0 ≤ t ^ pExp α * (Φ (x t) - Φ xstar) := mul_nonneg hT hN
  have h1 : lam α * pExp α / (2 * μ) * t ^ pExp α * (Φ (x t) - Φ xstar) ≤
      t ^ 2 / 2 * (t ^ pExp α * (Φ (x t) - Φ xstar)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hcoef hTN
  have h2 := h26.1.trans h26.2
  refine ⟨htp, hN, ?_, ?_⟩ <;> nlinarith [h1, h2, hEge]

theorem avd_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      Φ (x t) - Φ xstar
          ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) ∧
      2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
          = 2 * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
              * t ^ (-(2 / 3) * α) := by
  intro t ht
  obtain ⟨htp, hN, h3, -⟩ := avd_basic Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht
  have hex : t ^ (-pExp α - 2) = (t ^ pExp α * t ^ 2)⁻¹ := by
    have : -pExp α - 2 = -(pExp α + 2) := by ring
    rw [this, Real.rpow_neg htp.le, Real.rpow_add htp]
    norm_cast
  refine ⟨?_, ?_⟩
  · rw [hex, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  · have : -pExp α - 2 = -(2 / 3) * α := by unfold pExp; ring
    rw [this]
    rfl

theorem avd_exists_min {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ) :
    ∃ xstar : H, ∀ y, Φ xstar ≤ Φ y := by
  have hμ := hsc.1
  -- midpoint inequality
  have hmid : ∀ a b : H, 2 * Φ ((1 / 2 : ℝ) • (a + b)) + μ / 4 * ‖a - b‖ ^ 2 ≤ Φ a + Φ b := by
    intro a b
    set c : H := (1 / 2 : ℝ) • (a + b) with hc
    have h1 := hsc.2 c a
    have h2 := hsc.2 c b
    have e1 : a - c = (1 / 2 : ℝ) • (a - b) := by
      rw [hc]; module
    have e2 : b - c = -((1 / 2 : ℝ) • (a - b)) := by
      rw [hc]; module
    have e3 : c - a = -((1 / 2 : ℝ) • (a - b)) := by
      rw [hc]; module
    have e4 : c - b = (1 / 2 : ℝ) • (a - b) := by
      rw [hc]; module
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h1
    rw [e4] at h2
    rw [inner_smul_right] at h1
    rw [inner_neg_right, inner_smul_right] at h2
    rw [norm_neg, norm_smul] at h1
    rw [norm_smul] at h2
    simp only [Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 1 / 2 by norm_num)] at h1 h2
    nlinarith
  -- bounded below
  have hbdd : BddBelow (Set.range Φ) := by
    refine ⟨Φ 0 - ‖gradient Φ 0‖ ^ 2 / (2 * μ), ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hsc.2 0 y
    have hin : ⟪gradient Φ 0, y - 0⟫_ℝ ≥ -(‖gradient Φ 0‖ * ‖y‖) := by
      have := neg_abs_le (⟪gradient Φ 0, y - 0⟫_ℝ)
      have h2 := abs_real_inner_le_norm (gradient Φ 0) (y - 0)
      simp only [sub_zero] at *
      linarith
    simp only [sub_zero, norm_zero, zero_sub, norm_neg] at h hin
    have : Φ 0 - ‖gradient Φ 0‖ ^ 2 / (2 * μ) ≤ Φ y := by
      have hh : ‖gradient Φ 0‖ ^ 2 / (2 * μ) ≥ ‖gradient Φ 0‖ * ‖y‖ - μ / 2 * ‖y‖ ^ 2 := by
        rw [ge_iff_le, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖gradient Φ 0‖ - μ * ‖y‖)]
      linarith
    exact this
  set m := ⨅ y, Φ y with hm
  have hle : ∀ y, m ≤ Φ y := fun y => ciInf_le hbdd y
  have hseq : ∀ n : ℕ, ∃ y, Φ y < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt this
    exact ⟨y, hy⟩
  choose y hy using hseq
  have hcauchy : CauchySeq y := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / (μ * ε ^ 2))
    refine ⟨N, fun n hn => ?_⟩
    have hN1 : (0:ℝ) < (N : ℝ) + 1 := by positivity
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hd := hmid (y n) (y N)
    have h1 := hle ((1 / 2 : ℝ) • (y n + y N))
    have h2 := hy n
    have h3 := hy N
    have h4 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hN1 (by linarith)
    have e2N : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
    have hsq : μ / 4 * ‖y n - y N‖ ^ 2 < 2 / ((N : ℝ) + 1) := by linarith
    have h5 : 2 / ((N : ℝ) + 1) < μ / 4 * ε ^ 2 := by
      rw [div_lt_iff₀ hN1]
      have : 8 / (μ * ε ^ 2) * (μ * ε ^ 2) = 8 := by field_simp
      nlinarith [mul_pos hμ (pow_pos hε 2)]
    rw [dist_eq_norm]
    have : ‖y n - y N‖ ^ 2 < ε ^ 2 := by
      have := lt_trans hsq h5
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨ys, hys⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hcont : Continuous Φ := hΦ.continuous
  have hlim : Filter.Tendsto (fun n => Φ (y n)) Filter.atTop (nhds (Φ ys)) :=
    (hcont.tendsto ys).comp hys
  have hlim2 : Filter.Tendsto (fun n => Φ (y n)) Filter.atTop (nhds m) := by
    have hup : Filter.Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (m + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hle (y n)) (fun n => (hy n).le)
  have : Φ ys = m := tendsto_nhds_unique hlim hlim2
  exact ⟨ys, fun z => by rw [this]; exact hle z⟩

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v) :
    ∃ xstar : H, (∀ y, Φ xstar ≤ Φ y) ∧ (∀ z, (∀ y, Φ z ≤ Φ y) → z = xstar) ∧
      Tendsto x atTop (𝓝 xstar) ∧
      (fun t => Φ (x t) - Φ xstar) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) ∧
      (fun t => ‖x t - xstar‖ ^ 2) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) ∧
      (fun t => ‖v t‖ ^ 2) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) := by
  obtain ⟨xs, hxs⟩ := avd_exists_min Φ hΦ μ hsc
  have hμ := hsc.1
  set E1 := energyP Φ x v xs (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ) with hE1
  have hpos : ∀ t : ℝ, 0 < t → ‖t ^ (-(2 / 3) * α)‖ = t ^ (-(2 / 3) * α) := fun t ht =>
    Real.norm_of_nonneg (Real.rpow_pos_of_pos ht _).le
  have hev : ∀ᶠ t in atTop, t1 t₀ α μ ≤ t := Filter.eventually_ge_atTop _
  have ht1pos : 0 < t1 t₀ α μ := lt_of_lt_of_le hsol.1 (le_max_left _ _)
  have hev0 : ∀ᶠ t : ℝ in atTop, 0 < t := Filter.eventually_gt_atTop 0
  have hM : ∀ᶠ t in atTop, ‖x t - xs‖ ^ 2 ≤ 4 / μ * E1 * t ^ (-(2 / 3) * α) := by
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3⟩ := InertialAVD.StrongCvx.eq_28 Φ hΦ μ hsc α t₀ hα x v hsol xs hxs t ht
    linarith
  refine ⟨xs, hxs, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := avd_dist Φ μ hsc xs hxs z
    have : Φ z - Φ xs = 0 := le_antisymm (by linarith [hz xs]) (by linarith [hxs z])
    rw [this, mul_zero] at h
    have : ‖z - xs‖ = 0 := by nlinarith [norm_nonneg (z - xs)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · have hlim : Tendsto (fun t : ℝ => Real.sqrt (4 / μ * E1 * t ^ (-(2 / 3) * α))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => t ^ (-((2 / 3) * α))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by positivity)
      have h1 := h0.const_mul (4 / μ * E1)
      rw [mul_zero] at h1
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa [neg_mul, Function.comp_def] using h2
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim)
    filter_upwards [hM] with t ht
    exact Real.le_sqrt_of_sq_le ht
  · refine Asymptotics.IsBigO.of_bound (2 * E1) ?_
    filter_upwards [hev, hev0] with t ht ht0
    obtain ⟨h1, h2⟩ := avd_27 Φ hΦ μ hsc α t₀ hα x v hsol xs hxs t ht
    obtain ⟨-, hN, -, -⟩ := avd_basic Φ hΦ μ hsc α t₀ hα x v hsol xs hxs t ht
    rw [hpos t ht0, Real.norm_of_nonneg hN]
    linarith
  · refine Asymptotics.IsBigO.of_bound (4 / μ * E1) ?_
    filter_upwards [hM, hev0] with t ht ht0
    rw [hpos t ht0, Real.norm_of_nonneg (sq_nonneg _)]
    exact ht
  · refine Asymptotics.IsBigO.of_bound (4 * (1 + Real.sqrt (α / (α - 3))) ^ 2 * E1) ?_
    filter_upwards [hev, hev0] with t ht ht0
    have := InertialAVD.StrongCvx.thm_3_4_last_display Φ hΦ μ hsc α t₀ hα x v hsol xs hxs t ht
    rw [hpos t ht0, Real.norm_of_nonneg (sq_nonneg _)]
    exact this

end
