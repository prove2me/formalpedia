-- Prove2me | solution 2 for OAI.Cotype.exists_sector_timed_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:06:53.05589+00:00
-- url     : https://prove2.me/submissions/54b55870-2e0f-4da4-b4b1-73762afa6fa2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TimedShiftScalars.lean:L144-L169
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_sector_timed_shift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent

-- ---- from OAI.Analysis.Cotype.TimedShiftScalars ----
namespace OAI

noncomputable section
namespace Cotype

theorem exists_powerGapSectorSlope {ρ : ℝ} (hρ1 : 1 < ρ) (hρ2 : ρ < 2) :
    ∃ a : ℝ, 0 < a ∧ Real.exp (-a*Real.pi) = ρ-1 := by
  have hp : 0 < ρ-1 := by linarith
  have hl : Real.log (ρ-1) < 0 := Real.log_neg hp (by linarith)
  refine ⟨-Real.log (ρ-1) / Real.pi, div_pos (neg_pos.mpr hl) Real.pi_pos, ?_⟩
  convert Real.exp_log hp using 2
  field_simp

theorem complex_exp_negative_half_period (z : ℂ) (hz : z.im ≠ 0) :
    Complex.exp (-(z * ((Real.pi / |z.im| : ℝ) : ℂ))) =
      -(Real.exp (-z.re * (Real.pi / |z.im|)) : ℂ) := by
  by_cases hi : 0 < z.im
  · have ha : |z.im| = z.im := abs_of_pos hi
    have he : -(z * ((Real.pi / |z.im| : ℝ) : ℂ)) =
        ((-z.re * (Real.pi / |z.im|) : ℝ) : ℂ) - (Real.pi : ℂ)*Complex.I := by
      rw [ha]
      apply Complex.ext <;>
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.I_re, Complex.I_im, Complex.neg_im, Complex.mul_im,
          Complex.sub_im, mul_zero, sub_zero,
          add_zero, mul_one, zero_add]
      · ring
      · field_simp
        ring
    rw [he, Complex.exp_sub_pi_mul_I, Complex.ofReal_exp]
  · have hi' : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hi) hz
    have ha : |z.im| = -z.im := abs_of_neg hi'
    have he : -(z * ((Real.pi / |z.im| : ℝ) : ℂ)) =
        ((-z.re * (Real.pi / |z.im|) : ℝ) : ℂ) + (Real.pi : ℂ)*Complex.I := by
      rw [ha]
      apply Complex.ext <;>
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.neg_im, Complex.mul_im,
          Complex.add_re, Complex.add_im, mul_zero, sub_zero,
          add_zero, mul_one, zero_add]
      · ring
      · field_simp
    rw [he, Complex.exp_add_pi_mul_I, Complex.ofReal_exp]

theorem norm_half_period_shift (z : ℂ) (hz : z.im ≠ 0) :
    ‖1 - Complex.exp (-(z * ((Real.pi / |z.im| : ℝ) : ℂ)))‖ =
      1 + Real.exp (-z.re * (Real.pi / |z.im|)) := by
  rw [complex_exp_negative_half_period z hz, sub_neg_eq_add]
  have h : (1 : ℂ) + (Real.exp (-z.re * (Real.pi / |z.im|)) : ℂ) =
      ((1 + Real.exp (-z.re * (Real.pi / |z.im|)) : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem exp_time_interval_le (x : ℝ) {t s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    Real.exp (x*(s-t)) ≤ 1 + Real.exp (-x*t) := by
  by_cases hx : 0 ≤ x
  · have hh : x*(s-t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (sub_nonpos.mpr hs.2)
    exact (Real.exp_le_one_iff.mpr hh).trans (by linarith [Real.exp_pos (-x*t)])
  · have hh : x*(s-t) ≤ -x*t := by nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) hs.1]
    exact (Real.exp_le_exp.mpr hh).trans (by linarith)

theorem timed_shift_imaginary_data {a ρ : ℝ} (ha : 0 < a)
    (hexp : Real.exp (-a*Real.pi) = ρ-1) (z : ℂ) (hz : z.im ≠ 0)
    (hlow : -|z.im| ≤ z.re) (hhigh : z.re ≤ a*|z.im|) :
    ∃ t D : ℝ, 0 < t ∧ 0 ≤ D ∧
      ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ ∧
      (∀ s ∈ Set.Icc 0 t, Real.exp (z.re*(s-t)) ≤ D) ∧
      D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖ ≤ Real.pi*(a+2)/‖z‖ := by
  let t := Real.pi / |z.im|
  let D := 1 + Real.exp (-z.re*t)
  have hi : 0 < |z.im| := abs_pos.mpr hz
  have ht : 0 < t := div_pos Real.pi_pos hi
  have htπ : |z.im| *t = Real.pi := by dsimp [t]; field_simp
  have hDn : ‖1-Complex.exp (-(z*(t : ℂ)))‖ = D := norm_half_period_shift z hz
  have hDp : 0 < D := by dsimp [D]; positivity
  have hshift : ρ ≤ D := by
    have he : -a*Real.pi ≤ -z.re*t := by nlinarith [mul_le_mul_of_nonneg_right hhigh ht.le]
    have h := Real.exp_le_exp.mpr he
    rw [hexp] at h
    dsimp [D]
    linarith
  have hn : ‖z‖ ≤ (a+2)*|z.im| := by
    have hre : |z.re| ≤ (a+1)*|z.im| := by
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg ha.le hi.le]
    calc
      _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ (a+2)*|z.im| := by nlinarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro he; apply hz; simp [he])
  refine ⟨t, D, ht, hDp.le, hDn ▸ hshift, ?_, ?_⟩
  · exact fun s hs => exp_time_interval_le z.re hs
  · rw [hDn, mul_comm D t, mul_div_cancel_right₀ _ hDp.ne']
    apply (le_div_iff₀ hzn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hn ht.le]

theorem timed_shift_negative_data {ρ : ℝ} (hρ : ρ < 2)
    (z : ℂ) (hneg : z.re < -|z.im|) :
    ∃ t D : ℝ, 0 < t ∧ 0 ≤ D ∧
      ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ ∧
      (∀ s ∈ Set.Icc 0 t, Real.exp (z.re*(s-t)) ≤ D) ∧
      D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖ ≤ 8/‖z‖ := by
  have hr : z.re < 0 := lt_of_lt_of_le hneg (neg_nonpos.mpr (abs_nonneg _))
  let t := 2 / (-z.re)
  let D := Real.exp 2
  have ht : 0 < t := div_pos (by norm_num) (neg_pos.mpr hr)
  have hrt : -z.re*t = 2 := by dsimp [t]; field_simp [hr.ne]
  have he : ‖Complex.exp (-(z*(t : ℂ)))‖ = D := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    congr 1
    linarith
  have hD3 : 3 ≤ D := by dsimp [D]; linarith [Real.add_one_le_exp (2 : ℝ)]
  have hb : D-1 ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ := by
    have h := norm_sub_norm_le (Complex.exp (-(z*(t : ℂ)))) (1 : ℂ)
    rw [he, norm_one, norm_sub_rev] at h
    exact h
  have hbp : 0 < ‖1-Complex.exp (-(z*(t : ℂ)))‖ := by linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hr)
  have hn : ‖z‖ ≤ 2*(-z.re) := by
    calc
      _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2*(-z.re) := by rw [abs_of_neg hr]; linarith
  refine ⟨t, D, ht, by linarith, by linarith, ?_, ?_⟩
  · intro s hs
    apply Real.exp_le_exp.mpr
    have hh := mul_nonpos_of_nonpos_of_nonneg hr.le hs.1
    change z.re*(s-t) ≤ 2
    nlinarith
  · calc
      _ ≤ 2*t := by
        apply (div_le_iff₀ hbp).mpr
        have hh : D ≤ 2*‖1-Complex.exp (-(z*(t : ℂ)))‖ := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hh ht.le]
      _ ≤ 8/‖z‖ := by
        apply (le_div_iff₀ hzn).mpr
        nlinarith [mul_le_mul_of_nonneg_left hn ht.le]

theorem exists_sector_timed_shift {ρ : ℝ} (hρ1 : 1 < ρ) (hρ2 : ρ < 2) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧
      ∀ z : ℂ, z ≠ 0 → z.re ≤ a*|z.im| →
        ∃ t D : ℝ, 0 < t ∧ 0 ≤ D ∧
          ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ ∧
          (∀ s ∈ Set.Icc 0 t, Real.exp (z.re*(s-t)) ≤ D) ∧
          D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖ ≤ B/‖z‖ := by
  obtain ⟨a, ha, he⟩ := exists_powerGapSectorSlope hρ1 hρ2
  refine ⟨a, Real.pi*(a+2)+8, ha, by positivity, ?_⟩
  intro z hz hcone
  by_cases hn : z.re < -|z.im|
  · obtain ⟨t, D, ht, hD, hs, hi, hb⟩ := timed_shift_negative_data hρ2 z hn
    refine ⟨t, D, ht, hD, hs, hi, hb.trans ?_⟩
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) (norm_nonneg _)
  · have hlo : -|z.im| ≤ z.re := le_of_not_gt hn
    have him : z.im ≠ 0 := by
      intro hi
      have hr : z.re = 0 := by
        have hu : z.re ≤ 0 := by simpa [hi] using hcone
        have hl : 0 ≤ z.re := by simpa [hi] using hlo
        exact le_antisymm hu hl
      apply hz
      exact Complex.ext (by simpa using hr) (by simpa using hi)
    obtain ⟨t, D, ht, hD, hs, hi, hb⟩ := timed_shift_imaginary_data ha he z him hlo hcone
    refine ⟨t, D, ht, hD, hs, hi, hb.trans ?_⟩
    exact div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.exists_sector_timed_shift := @_root_.OAI.Cotype.exists_sector_timed_shift
