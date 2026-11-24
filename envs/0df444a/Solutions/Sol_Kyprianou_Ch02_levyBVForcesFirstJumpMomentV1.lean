-- Prove2me | solution 1 for Kyprianou.Ch02.levyBVForcesFirstJumpMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T05:37:16.564661+00:00
-- url     : https://prove2.me/submissions/6b65d90c-0302-4a65-b404-fcee1ef35196

import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyBVExponentialGridPowerLowerBoundV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_re_one_sub_charFun_eq_integral

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

private lemma grid_laplace_deficit
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ q n ^ (n + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ((n : ℝ) + 1) * (1 - q n) ≤ C := by
  obtain ⟨c, hc, hpow⟩ := h
  have hc1 : c ≤ 1 := by
    have h0 := hpow 0
    simp only [zero_add, pow_one] at h0
    exact h0.trans (hq 0).2
  refine ⟨-Real.log c, by linarith [Real.log_nonpos hc.le hc1], fun n => ?_⟩
  have hp : 0 < q n := by
    by_contra hn
    have he : q n = 0 := le_antisymm (le_of_not_gt hn) (hq n).1
    have hh := hpow n
    rw [he, zero_pow (Nat.succ_ne_zero n)] at hh
    linarith
  have hl := Real.log_le_log hc (hpow n)
  rw [Real.log_pow] at hl
  have hm := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp)
    (show 0 ≤ (n : ℝ) + 1 by positivity)
  push_cast at hl
  linarith

private lemma exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hprod : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [Real.exp_pos (-1 : ℝ)]

private lemma half_mul_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - u by linarith) hu0 (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_zero, zero_add, mul_one] at hc
  have harg : u * (-1 : ℝ) = -u := by ring
  rw [harg] at hc
  have hexp1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := exp_neg_one_le_half
  nlinarith

private lemma tail_inv_sq_lintegral {c : ℝ} (hc : 0 < c) :
    (∫⁻ ξ in Set.Ioi c, ENNReal.ofReal (2 / ξ ^ 2)) = ENNReal.ofReal (2 * c⁻¹) := by
  have hi : IntegrableOn (fun ξ : ℝ => 2 * ξ ^ (-2 : ℝ)) (Set.Ioi c) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul 2
  have hval : (∫ ξ in Set.Ioi c, 2 * ξ ^ (-2 : ℝ)) = 2 * c⁻¹ := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi c)] (fun ξ : ℝ => 2 * ξ ^ (-2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hc.trans hξ).le _)
  have hlin := ofReal_integral_eq_lintegral_ofReal hi hnn
  rw [hval] at hlin
  rw [hlin]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hξpos : 0 < ξ := hc.trans hξ
  rw [Real.rpow_neg hξpos.le, Real.rpow_two, div_eq_mul_inv]

private lemma measurable_two_div_sq :
    Measurable (fun ξ : ℝ => ENNReal.ofReal (2 / ξ ^ 2)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const 2))

private lemma measurable_cauchy_cos_kernel_left (x : ℝ) :
    Measurable (fun ξ : ℝ => ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2))) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_const.sub (Real.continuous_cos.measurable.comp (measurable_id.mul measurable_const))).div
      (measurable_const.add (measurable_id.pow_const 2)))

private lemma kernel_lintegral_le_eight_exp_deficit (y : ℝ) :
    (∫⁻ ξ in Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos (ξ * y)) / (1 + ξ ^ 2))) ≤
      8 * ENNReal.ofReal (1 - Real.exp (-|y|)) := by
  have hcos_abs : ∀ ξ : ℝ, Real.cos (ξ * y) = Real.cos (ξ * |y|) := by
    intro ξ
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, mul_neg, Real.cos_neg]
  simp_rw [hcos_abs]
  set u : ℝ := |y|
  have hu0 : 0 ≤ u := abs_nonneg y
  rcases eq_or_lt_of_le hu0 with hu_zero | hupos
  · rw [← hu_zero]
    simp
  · rcases lt_or_ge u 1 with hu1 | hu1
    · have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) u⁻¹ ∪ Set.Ioi u⁻¹ := by
        ext ξ
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hξ
          rcases le_or_gt ξ u⁻¹ with hle | hgt
          · exact Or.inl ⟨hξ, hle⟩
          · exact Or.inr hgt
        · rintro (⟨hξ, _⟩ | hgt)
          · exact hξ
          · exact (inv_pos.mpr hupos).trans hgt
      have hhead :
          (∫⁻ ξ in Set.Ioc (0 : ℝ) u⁻¹,
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) ≤
            ENNReal.ofReal (u / 2) := by
        calc
          (∫⁻ ξ in Set.Ioc (0 : ℝ) u⁻¹,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
            ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) u⁻¹, ENNReal.ofReal (u ^ 2 / 2) := by
                refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
                have hc : 1 - Real.cos (ξ * u) ≤ (ξ * u) ^ 2 / 2 := by
                  linarith [Real.one_sub_sq_div_two_le_cos (x := ξ * u)]
                have hden : 0 < 1 + ξ ^ 2 := by positivity
                rw [div_le_iff₀ hden]
                nlinarith [sq_nonneg ξ, sq_nonneg u]
          _ = ENNReal.ofReal (u ^ 2 / 2) * volume (Set.Ioc (0 : ℝ) u⁻¹) := by
                simp
          _ = ENNReal.ofReal (u ^ 2 / 2) * ENNReal.ofReal u⁻¹ := by
                rw [Real.volume_Ioc, sub_zero]
          _ = ENNReal.ofReal (u / 2) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                field_simp [hupos.ne']
      have htail :
          (∫⁻ ξ in Set.Ioi u⁻¹,
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) ≤
            ENNReal.ofReal (2 * u) := by
        calc
          (∫⁻ ξ in Set.Ioi u⁻¹,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
            ≤ ∫⁻ ξ in Set.Ioi u⁻¹, ENNReal.ofReal (2 / ξ ^ 2) := by
                refine setLIntegral_mono measurable_two_div_sq fun ξ hξ =>
                  ENNReal.ofReal_le_ofReal ?_
                have hξpos : 0 < ξ := (inv_pos.mpr hupos).trans hξ
                have hc : 1 - Real.cos (ξ * u) ≤ 2 := by
                  linarith [Real.neg_one_le_cos (ξ * u)]
                have h1 : (1 - Real.cos (ξ * u)) / (1 + ξ ^ 2) ≤ 2 / (1 + ξ ^ 2) :=
                  div_le_div_of_nonneg_right hc (by positivity)
                have h2 : 2 / (1 + ξ ^ 2) ≤ 2 / ξ ^ 2 :=
                  div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hξpos) (by linarith)
                exact h1.trans h2
          _ = ENNReal.ofReal (2 * (u⁻¹)⁻¹) := tail_inv_sq_lintegral (inv_pos.mpr hupos)
          _ = ENNReal.ofReal (2 * u) := by rw [inv_inv]
      have hexp : u / 2 ≤ 1 - Real.exp (-u) := half_mul_le_one_sub_exp_neg hupos.le hu1.le
      calc
        (∫⁻ ξ in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
          ≤ (∫⁻ ξ in Set.Ioc (0 : ℝ) u⁻¹,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) +
            (∫⁻ ξ in Set.Ioi u⁻¹,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) := by
              rw [hsplit]
              exact lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (u / 2) + ENNReal.ofReal (2 * u) := add_le_add hhead htail
        _ = ENNReal.ofReal (5 / 2 * u) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
        _ ≤ ENNReal.ofReal (8 * (1 - Real.exp (-u))) :=
              ENNReal.ofReal_le_ofReal (by linarith)
        _ = 8 * ENNReal.ofReal (1 - Real.exp (-u)) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    · have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 := by
        ext ξ
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hξ
          rcases le_or_gt ξ 1 with hle | hgt
          · exact Or.inl ⟨hξ, hle⟩
          · exact Or.inr hgt
        · rintro (⟨hξ, _⟩ | hgt)
          · exact hξ
          · linarith
      have hhead :
          (∫⁻ ξ in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) ≤
            ENNReal.ofReal 2 := by
        calc
          (∫⁻ ξ in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
            ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal 2 := by
                refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
                have hc : 1 - Real.cos (ξ * u) ≤ 2 := by
                  linarith [Real.neg_one_le_cos (ξ * u)]
                have hden : 0 < 1 + ξ ^ 2 := by positivity
                rw [div_le_iff₀ hden]
                nlinarith [sq_nonneg ξ]
          _ = ENNReal.ofReal 2 * volume (Set.Ioc (0 : ℝ) 1) := by simp
          _ = ENNReal.ofReal 2 := by rw [Real.volume_Ioc]; norm_num
      have htail :
          (∫⁻ ξ in Set.Ioi (1 : ℝ),
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) ≤
            ENNReal.ofReal 2 := by
        calc
          (∫⁻ ξ in Set.Ioi (1 : ℝ),
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
            ≤ ∫⁻ ξ in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 / ξ ^ 2) := by
                refine setLIntegral_mono measurable_two_div_sq fun ξ hξ =>
                  ENNReal.ofReal_le_ofReal ?_
                have hξpos : 0 < ξ := zero_lt_one.trans hξ
                have hc : 1 - Real.cos (ξ * u) ≤ 2 := by
                  linarith [Real.neg_one_le_cos (ξ * u)]
                have h1 : (1 - Real.cos (ξ * u)) / (1 + ξ ^ 2) ≤ 2 / (1 + ξ ^ 2) :=
                  div_le_div_of_nonneg_right hc (by positivity)
                have h2 : 2 / (1 + ξ ^ 2) ≤ 2 / ξ ^ 2 :=
                  div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hξpos) (by linarith)
                exact h1.trans h2
          _ = ENNReal.ofReal (2 * (1 : ℝ)⁻¹) := tail_inv_sq_lintegral one_pos
          _ = ENNReal.ofReal 2 := by norm_num
      have hexp : 1 / 2 ≤ 1 - Real.exp (-u) := by
        have hle : Real.exp (-u) ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr (by linarith)
        linarith [exp_neg_one_le_half]
      calc
        (∫⁻ ξ in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2)))
          ≤ (∫⁻ ξ in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) +
            (∫⁻ ξ in Set.Ioi (1 : ℝ),
              ENNReal.ofReal ((1 - Real.cos (ξ * u)) / (1 + ξ ^ 2))) := by
              rw [hsplit]
              exact lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal 2 + ENNReal.ofReal 2 := add_le_add hhead htail
        _ = ENNReal.ofReal 4 := by
              rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
              norm_num
        _ ≤ ENNReal.ofReal (8 * (1 - Real.exp (-u))) :=
              ENNReal.ofReal_le_ofReal (by linarith)
        _ = 8 * ENNReal.ofReal (1 - Real.exp (-u)) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private lemma kernel_lintegral_ge_small_abs {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ENNReal.ofReal (|x| / 128) ≤
      ∫⁻ ξ in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) := by
  set u : ℝ := |x|
  have hu1 : u < 1 := abs_lt.mpr hx
  have hu_nn : 0 ≤ u := abs_nonneg x
  rcases eq_or_lt_of_le hu_nn with hu0 | hupos
  · rw [← hu0]
    simp
  · let J : Set ℝ := Set.Icc ((2 * u)⁻¹) u⁻¹
    have hJsub : J ⊆ Set.Ioi (0 : ℝ) := by
      intro ξ hξ
      exact lt_of_lt_of_le (by positivity) hξ.1
    have hpt : ∀ ξ ∈ J, u ^ 2 / 64 ≤ (1 - Real.cos (ξ * x)) / (1 + ξ ^ 2) := by
      intro ξ hξ
      have hξpos : 0 < ξ := lt_of_lt_of_le (by positivity) hξ.1
      have hmul_lo : 1 / 2 ≤ ξ * u := by
        have h := mul_le_mul_of_nonneg_right hξ.1 hupos.le
        have h2 : (2 * u)⁻¹ * u = 1 / 2 := by field_simp [hupos.ne']
        linarith
      have hmul_hi : ξ * u ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hξ.2 hupos.le
        rwa [inv_mul_cancel₀ hupos.ne'] at h
      have habs : |ξ * x| ≤ Real.pi := by
        rw [abs_mul, abs_of_pos hξpos]
        linarith [Real.two_le_pi]
      have hcos := Real.cos_le_one_sub_mul_cos_sq habs
      have hsq_eq : (ξ * x) ^ 2 = (ξ * u) ^ 2 := by
        dsimp [u]
        rw [mul_pow, mul_pow, sq_abs]
      have hsq_lo : (1 / 4 : ℝ) ≤ (ξ * x) ^ 2 := by
        rw [hsq_eq]
        nlinarith
      have hpi2 : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
        have hpi4 : Real.pi ^ 2 ≤ 16 := by
          nlinarith [Real.pi_pos, Real.pi_le_four]
        rw [div_le_div_iff₀ (by norm_num) (sq_pos_of_pos Real.pi_pos)]
        linarith
      have hnum : (1 / 32 : ℝ) ≤ 1 - Real.cos (ξ * x) := by
        have hprod : (1 / 8 : ℝ) * (1 / 4) ≤ (2 / Real.pi ^ 2) * (ξ * x) ^ 2 :=
          mul_le_mul hpi2 hsq_lo (by norm_num) (by positivity)
        linarith
      have huinv_ge_one : 1 ≤ u⁻¹ := (one_le_inv₀ hupos).mpr hu1.le
      have hden_le : 1 + ξ ^ 2 ≤ 2 * (u⁻¹) ^ 2 := by
        have hξ2 : ξ ^ 2 ≤ (u⁻¹) ^ 2 := pow_le_pow_left₀ hξpos.le hξ.2 2
        have h1 : (1 : ℝ) ≤ (u⁻¹) ^ 2 := by nlinarith
        linarith
      have hden_pos : 0 < 1 + ξ ^ 2 := by positivity
      calc
        u ^ 2 / 64 = (1 / 32 : ℝ) / (2 * (u⁻¹) ^ 2) := by field_simp [hupos.ne']; ring
        _ ≤ (1 / 32 : ℝ) / (1 + ξ ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le
        _ ≤ (1 - Real.cos (ξ * x)) / (1 + ξ ^ 2) :=
          div_le_div_of_nonneg_right hnum hden_pos.le
    calc
      ENNReal.ofReal (u / 128)
        = ENNReal.ofReal (u ^ 2 / 64) * ENNReal.ofReal (u⁻¹ - (2 * u)⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp [hupos.ne']
            ring
      _ = ∫⁻ _ in J, ENNReal.ofReal (u ^ 2 / 64) := by
            simp [J, Real.volume_Icc]
      _ ≤ ∫⁻ ξ in J, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) :=
            setLIntegral_mono (measurable_cauchy_cos_kernel_left x)
              fun ξ hξ => ENNReal.ofReal_le_ofReal (hpt ξ hξ)
      _ ≤ ∫⁻ ξ in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) :=
            lintegral_mono' (Measure.restrict_mono hJsub le_rfl) le_rfl

private lemma compensated_re_eq (ξ x : ℝ) :
    (ProbabilityTheory.levyCompensatedIntegrand ξ x).re = Real.cos (ξ * x) - 1 := by
  unfold ProbabilityTheory.levyCompensatedIntegrand
  have hexp : (Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I)).re = Real.cos (ξ * x) := by
    have harg : (x : ℂ) * (ξ : ℂ) * Complex.I = (((ξ * x : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_mul]
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  split_ifs
  · simp only [mul_one, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      add_zero, sub_zero, hexp]
  · simp only [mul_zero, sub_zero, Complex.sub_re, Complex.one_re, hexp]

private lemma neg_re_levyTripleExponent_ge
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ξ * x)) ∂T.levyMeasure) ≤
      ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re) := by
  have hIntC : Integrable (ProbabilityTheory.levyCompensatedIntegrand ξ) T.levyMeasure :=
    ProbabilityTheory.integrable_levyCompensatedIntegrand T.levyMeasure_isLevyMeasure ξ
  have hIntRe : Integrable (fun x => (ProbabilityTheory.levyCompensatedIntegrand ξ x).re)
      T.levyMeasure :=
    Complex.reCLM.integrable_comp hIntC
  have hIntCos : Integrable (fun x => 1 - Real.cos (ξ * x)) T.levyMeasure := by
    refine hIntRe.neg.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, compensated_re_eq]
    ring
  have hIntEq : (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure).re =
      -∫ x, (1 - Real.cos (ξ * x)) ∂T.levyMeasure := by
    have hcomm := (Complex.reCLM.integral_comp_comm hIntC).symm
    change (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure).re =
      ∫ x, (ProbabilityTheory.levyCompensatedIntegrand ξ x).re ∂T.levyMeasure at hcomm
    rw [hcomm, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [compensated_re_eq]
    ring
  have hnn : 0 ≤ᵐ[T.levyMeasure] (fun x : ℝ => 1 - Real.cos (ξ * x)) :=
    Filter.Eventually.of_forall fun x => by
      change (0 : ℝ) ≤ 1 - Real.cos (ξ * x)
      linarith [Real.cos_le_one (ξ * x)]
  rw [← ofReal_integral_eq_lintegral_ofReal hIntCos hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold Kyprianou.Ch01.levyTripleExponent
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_self, zero_sub]
  rw [hIntEq]
  have hg : 0 ≤ (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 := by positivity
  linarith

/-- Almost-sure locally bounded variation of a real Lévy process forces
integrability of `min 1 |x|` against its Lévy measure. -/
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) →
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure := by
  intro hBV
  have : SigmaFinite levyMeasure := hlevyMeasure.sigmaFinite
  let T : ProbabilityTheory.LevyKhintchineTriple := ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩
  let μξ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let tSeq : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  let q : ℕ → ℝ := fun n => ∫ ω, Real.exp (-|X (tSeq n) ω|) ∂P
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1 := by
    intro n
    refine ⟨integral_nonneg fun _ => Real.exp_nonneg _, ?_⟩
    calc
      q n ≤ ∫ _ : Ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
          (integrable_const _)
          (Filter.Eventually.of_forall fun _ =>
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))
      _ = 1 := by simp
  obtain ⟨C, hC0, hCbound⟩ :=
    grid_laplace_deficit q hq
      (Kyprianou.Ch02.levyBVExponentialGridPowerLowerBoundV1 P X hX hBV)
  -- Step 1: Bound the scaled Cauchy-weighted characteristic-function defect at time tSeq n.
  let F : ℕ → ℝ → ℝ≥0∞ := fun n ξ =>
    ENNReal.ofReal (((n : ℝ) + 1) * (1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2))
  have hF_meas : ∀ n, Measurable (F n) := by
    intro n
    have : IsProbabilityMeasure (P.map (X (tSeq n))) :=
      Measure.isProbabilityMeasure_map (hcoord (tSeq n))
    have hcont_cf : Continuous (charFun (P.map (X (tSeq n)))) :=
      MeasureTheory.continuous_charFun
    have hcont : Continuous (fun ξ : ℝ =>
        ((n : ℝ) + 1) * (1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2)) :=
      ((continuous_const.mul (continuous_const.sub (Complex.continuous_re.comp hcont_cf))).div
        (continuous_const.add (continuous_pow 2)) fun ξ => by positivity)
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have hF_lintegral : ∀ n : ℕ, (∫⁻ ξ, F n ξ ∂μξ) ≤ 8 * ENNReal.ofReal C := by
    intro n
    have : IsProbabilityMeasure (P.map (X (tSeq n))) :=
      Measure.isProbabilityMeasure_map (hcoord (tSeq n))
    obtain ⟨X_meas, hX_meas, hX_ae⟩ := hcoord (tSeq n)
    have hXexp_int : Integrable (fun ω => Real.exp (-|X (tSeq n) ω|)) P := by
      refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact ((Real.continuous_exp.measurable.comp (measurable_neg.comp measurable_abs)).comp_aemeasurable
          (hcoord (tSeq n))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
    have h1_sub_exp : (∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-|X (tSeq n) ω|)) ∂P) =
        ENNReal.ofReal (1 - q n) := by
      have hi : Integrable (fun ω => 1 - Real.exp (-|X (tSeq n) ω|)) P :=
        (integrable_const 1).sub hXexp_int
      have hnn : 0 ≤ᵐ[P] (fun ω => 1 - Real.exp (-|X (tSeq n) ω|)) :=
        Filter.Eventually.of_forall fun ω => by
          change (0 : ℝ) ≤ 1 - Real.exp (-|X (tSeq n) ω|)
          have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg (X (tSeq n) ω)))
          linarith
      rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, integral_sub (integrable_const 1) hXexp_int]
      simp [q]
    have hinner : ∀ ξ : ℝ,
        ENNReal.ofReal ((1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2)) =
          ∫⁻ ω, ENNReal.ofReal ((1 - Real.cos (ξ * X_meas ω)) / (1 + ξ ^ 2)) ∂P := by
      intro ξ
      have hcf := ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral
        (μ := P.map (X (tSeq n))) ξ
      have hmap : (∫ x, (1 - Real.cos (ξ * x)) ∂(P.map (X (tSeq n)))) =
          ∫ ω, (1 - Real.cos (ξ * X (tSeq n) ω)) ∂P := by
        refine integral_map (hcoord (tSeq n)) ?_
        exact (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
      have hcos_int : Integrable (fun ω => (1 - Real.cos (ξ * X (tSeq n) ω)) / (1 + ξ ^ 2)) P := by
        refine (integrable_const (2 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
        · have hm : Measurable (fun x : ℝ => (1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) :=
            (measurable_const.sub (Real.continuous_cos.measurable.comp
              (measurable_const.mul measurable_id))).div (measurable_const.add (measurable_const))
          exact (hm.comp_aemeasurable (hcoord (tSeq n))).aestronglyMeasurable
        · have hnn : 0 ≤ (1 - Real.cos (ξ * X (tSeq n) ω)) / (1 + ξ ^ 2) :=
            div_nonneg (by linarith [Real.cos_le_one (ξ * X (tSeq n) ω)]) (by positivity)
          rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_le_iff₀ (by positivity)]
          have hc : 1 - Real.cos (ξ * X (tSeq n) ω) ≤ 2 := by
            linarith [Real.neg_one_le_cos (ξ * X (tSeq n) ω)]
          nlinarith [sq_nonneg ξ]
      have hnn : 0 ≤ᵐ[P] (fun ω => (1 - Real.cos (ξ * X (tSeq n) ω)) / (1 + ξ ^ 2)) :=
        Filter.Eventually.of_forall fun ω => by
          change (0 : ℝ) ≤ (1 - Real.cos (ξ * X (tSeq n) ω)) / (1 + ξ ^ 2)
          exact div_nonneg (by linarith [Real.cos_le_one (ξ * X (tSeq n) ω)]) (by positivity)
      have hlhs :
          ENNReal.ofReal ((1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2)) =
            ∫⁻ ω, ENNReal.ofReal ((1 - Real.cos (ξ * X (tSeq n) ω)) / (1 + ξ ^ 2)) ∂P := by
        rw [← ofReal_integral_eq_lintegral_ofReal hcos_int hnn, integral_div, ← hmap, ← hcf]
        simp only [Complex.sub_re, Complex.one_re]
      exact hlhs.trans (lintegral_congr_ae (hX_ae.mono fun ω hω => by dsimp only; rw [hω]))
    have hm_prod :
        Measurable (Function.uncurry fun (ω : Ω) (ξ : ℝ) =>
          ENNReal.ofReal ((1 - Real.cos (ξ * X_meas ω)) / (1 + ξ ^ 2))) := by
      change Measurable (fun z : Ω × ℝ =>
        ENNReal.ofReal ((1 - Real.cos (z.2 * X_meas z.1)) / (1 + z.2 ^ 2)))
      exact ENNReal.measurable_ofReal.comp
        ((measurable_const.sub (Real.continuous_cos.measurable.comp
          (measurable_snd.mul (hX_meas.comp measurable_fst)))).div
          (measurable_const.add (measurable_snd.pow_const 2)))
    have hFn_eq : ∀ ξ : ℝ,
        F n ξ = ENNReal.ofReal ((n : ℝ) + 1) *
          ENNReal.ofReal ((1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2)) := by
      intro ξ
      dsimp [F]
      rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity)]
    have hback :
        (∫⁻ ω, 8 * ENNReal.ofReal (1 - Real.exp (-|X_meas ω|)) ∂P) =
          ∫⁻ ω, 8 * ENNReal.ofReal (1 - Real.exp (-|X (tSeq n) ω|)) ∂P :=
      lintegral_congr_ae (hX_ae.symm.mono fun ω hω => by dsimp only; rw [hω])
    calc
      (∫⁻ ξ, F n ξ ∂μξ)
        = ENNReal.ofReal ((n : ℝ) + 1) *
            ∫⁻ ξ, ENNReal.ofReal ((1 - (charFun (P.map (X (tSeq n))) ξ).re) / (1 + ξ ^ 2)) ∂μξ := by
            simp_rw [hFn_eq]
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((n : ℝ) + 1) *
            ∫⁻ ξ, (∫⁻ ω, ENNReal.ofReal ((1 - Real.cos (ξ * X_meas ω)) / (1 + ξ ^ 2)) ∂P) ∂μξ := by
            simp_rw [hinner]
      _ = ENNReal.ofReal ((n : ℝ) + 1) *
            ∫⁻ ω, (∫⁻ ξ, ENNReal.ofReal ((1 - Real.cos (ξ * X_meas ω)) / (1 + ξ ^ 2)) ∂μξ) ∂P := by
            rw [lintegral_lintegral_swap hm_prod.aemeasurable]
      _ ≤ ENNReal.ofReal ((n : ℝ) + 1) *
            ∫⁻ ω, 8 * ENNReal.ofReal (1 - Real.exp (-|X_meas ω|)) ∂P :=
            mul_le_mul_right (lintegral_mono fun ω =>
              kernel_lintegral_le_eight_exp_deficit (X_meas ω)) _
      _ = 8 * (ENNReal.ofReal ((n : ℝ) + 1) * ENNReal.ofReal (1 - q n)) := by
            rw [hback, lintegral_const_mul' _ _ (by norm_num : (8 : ℝ≥0∞) ≠ ⊤), h1_sub_exp]
            ring
      _ ≤ 8 * ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hCbound n)) 8
  -- Step 2: Pass to n → ∞ via Fatou's lemma.
  have hlim_pt : ∀ ξ : ℝ,
      ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)) ≤
        Filter.liminf (fun n => F n ξ) atTop := by
    intro ξ
    let hStep : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
    have ht0 : Tendsto hStep atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have htne : Tendsto hStep atTop (𝓝[≠] (0 : ℝ)) := by
      rw [nhdsWithin, tendsto_inf]
      exact ⟨ht0, tendsto_principal.mpr (Filter.Eventually.of_forall fun n => by
        dsimp [hStep]; exact ne_of_gt (by positivity))⟩
    have hexp_lim :=
      (ProbabilityTheory.leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
        (Kyprianou.Ch01.levyTripleExponent T ξ)).comp htne
    have hdiv_lim :
        Tendsto (fun n : ℕ =>
            ((hStep n)⁻¹ *
              (1 - Complex.exp (↑(hStep n) * Kyprianou.Ch01.levyTripleExponent T ξ)).re) /
              (1 + ξ ^ 2))
          atTop
          (𝓝 (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2))) := by
      simpa only [Complex.neg_re, Function.comp_apply] using hexp_lim.div_const (1 + ξ ^ 2)
    have hofReal_lim :
        Tendsto (fun n : ℕ => F n ξ) atTop
          (𝓝 (ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)))) := by
      have hc := (ENNReal.continuous_ofReal.tendsto _).comp hdiv_lim
      refine hc.congr fun n => ?_
      dsimp [F, hStep, tSeq]
      rw [inv_inv, hchar (((n : ℝ≥0) + 1)⁻¹) ξ]
      have hcast : (((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) : ℂ) = ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast]
    rw [hofReal_lim.liminf_eq]
  have hFatou :
      (∫⁻ ξ, ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)) ∂μξ) ≤
        8 * ENNReal.ofReal C := by
    calc
      (∫⁻ ξ, ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)) ∂μξ)
        ≤ ∫⁻ ξ, Filter.liminf (fun n => F n ξ) atTop ∂μξ := lintegral_mono hlim_pt
      _ ≤ Filter.liminf (fun n => ∫⁻ ξ, F n ξ ∂μξ) atTop := lintegral_liminf_le hF_meas
      _ ≤ 8 * ENNReal.ofReal C := by
            rw [Filter.liminf_eq]
            refine sSup_le fun b hb => ?_
            obtain ⟨n, hn⟩ := hb.exists
            exact hn.trans (hF_lintegral n)
  -- Step 3: Lower-bound -Re(Ψ(ξ)) by the jump integral and swap ξ and x by Tonelli.
  have hTonelli2 :
      (∫⁻ x, (∫⁻ ξ, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) ∂μξ) ∂levyMeasure) ≤
        8 * ENNReal.ofReal C := by
    have hm2 : Measurable (Function.uncurry fun (ξ x : ℝ) =>
        ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2))) := by
      change Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((1 - Real.cos (p.1 * p.2)) / (1 + p.1 ^ 2)))
      exact ENNReal.measurable_ofReal.comp
        ((measurable_const.sub (Real.continuous_cos.measurable.comp
          (measurable_fst.mul measurable_snd))).div
          (measurable_const.add (measurable_fst.pow_const 2)))
    calc
      (∫⁻ x, (∫⁻ ξ, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) ∂μξ) ∂levyMeasure)
        = ∫⁻ ξ, (∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) ∂levyMeasure) ∂μξ :=
            (lintegral_lintegral_swap hm2.aemeasurable).symm
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)) ∂μξ := by
            refine lintegral_mono fun ξ => ?_
            have hdiv : ∀ x : ℝ,
                ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) =
                  ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) * ENNReal.ofReal (1 - Real.cos (ξ * x)) := by
              intro x
              rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
            simp_rw [hdiv]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            calc
              ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) *
                  (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ξ * x)) ∂levyMeasure)
                ≤ ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) *
                    ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re) :=
                  mul_le_mul_right (neg_re_levyTripleExponent_ge T ξ) _
              _ = ENNReal.ofReal (-(Kyprianou.Ch01.levyTripleExponent T ξ).re / (1 + ξ ^ 2)) := by
                  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div]
      _ ≤ 8 * ENNReal.ofReal C := hFatou
  -- Step 4: Conclude finite small-jump first moment and combine with finite large-jump mass.
  have hsmall_div :
      (∫⁻ x in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal (|x| / 128) ∂levyMeasure) ≤
        8 * ENNReal.ofReal C := by
    calc
      (∫⁻ x in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal (|x| / 128) ∂levyMeasure)
        ≤ ∫⁻ x in Set.Ioo (-1 : ℝ) 1,
            (∫⁻ ξ, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) ∂μξ) ∂levyMeasure :=
          setLIntegral_mono' measurableSet_Ioo fun x hx => kernel_lintegral_ge_small_abs hx
      _ ≤ ∫⁻ x, (∫⁻ ξ, ENNReal.ofReal ((1 - Real.cos (ξ * x)) / (1 + ξ ^ 2)) ∂μξ) ∂levyMeasure :=
          setLIntegral_le_lintegral _ _
      _ ≤ 8 * ENNReal.ofReal C := hTonelli2
  have hsmall_lt_top :
      (∫⁻ x in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal |x| ∂levyMeasure) < ⊤ := by
    have hfactor : ∀ x : ℝ,
        ENNReal.ofReal |x| = (128 : ℝ≥0∞) * ENNReal.ofReal (|x| / 128) := by
      intro x
      have h128 : (128 : ℝ≥0∞) = ENNReal.ofReal 128 := by norm_num
      rw [h128, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    simp_rw [hfactor]
    rw [lintegral_const_mul' _ _ (by norm_num : (128 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_lt_top (by norm_num)
      (lt_of_le_of_lt hsmall_div (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top))
  have hlarge_lt_top : levyMeasure {x : ℝ | 1 ≤ |x|} < ⊤ :=
    hlevyMeasure.measure_setOf_abs_ge_lt_top one_pos
  refine ⟨(continuous_const.min continuous_abs).measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hpt : ∀ x : ℝ,
      ENNReal.ofReal ‖min (1 : ℝ) |x|‖ ≤
        (Set.Ioo (-1 : ℝ) 1).indicator (fun y => ENNReal.ofReal |y|) x +
          {y : ℝ | 1 ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    have hnn : 0 ≤ min (1 : ℝ) |x| := le_min zero_le_one (abs_nonneg x)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    rcases lt_or_ge |x| 1 with hlt | hge
    · have hx : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hlt
      rw [min_eq_right hlt.le, Set.indicator_of_mem hx]
      exact le_self_add
    · have hx : x ∈ {y : ℝ | 1 ≤ |y|} := hge
      rw [min_eq_left hge, ENNReal.ofReal_one, Set.indicator_of_mem hx]
      exact le_add_self
  have hmeas_large : MeasurableSet {y : ℝ | 1 ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  calc
    (∫⁻ x, ENNReal.ofReal ‖min (1 : ℝ) |x|‖ ∂levyMeasure)
      ≤ ∫⁻ x, ((Set.Ioo (-1 : ℝ) 1).indicator (fun y => ENNReal.ofReal |y|) x +
          {y : ℝ | 1 ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) x) ∂levyMeasure :=
        lintegral_mono hpt
    _ = (∫⁻ x, (Set.Ioo (-1 : ℝ) 1).indicator (fun y => ENNReal.ofReal |y|) x ∂levyMeasure) +
          (∫⁻ x, {y : ℝ | 1 ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂levyMeasure) :=
        lintegral_add_left
          ((ENNReal.measurable_ofReal.comp continuous_abs.measurable).indicator measurableSet_Ioo) _
    _ = (∫⁻ x in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal |x| ∂levyMeasure) +
          levyMeasure {y : ℝ | 1 ≤ |y|} := by
        rw [lintegral_indicator measurableSet_Ioo, lintegral_indicator hmeas_large]
        simp
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hsmall_lt_top, hlarge_lt_top⟩
