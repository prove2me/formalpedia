-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12300158-c1db-56fd-8013-34ceb1c1bf00

import Mathlib
import Theorems.Thm_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral

set_option autoImplicit false

open MeasureTheory Set Real

namespace OcSigma

theorem two_mul_sq_le_cosh_two_mul_sub_one (σ : ℝ) : 2 * σ ^ 2 ≤ Real.cosh (2 * σ) - 1 := by
  have h1 : Real.cosh (2 * σ) = 1 + 2 * Real.sinh σ ^ 2 := by
    rw [Real.cosh_two_mul, Real.cosh_sq]; ring
  have h2 : σ ^ 2 ≤ Real.sinh σ ^ 2 := by
    rcases le_or_gt 0 σ with h | h
    · have := Real.self_le_sinh_iff.2 h
      exact pow_le_pow_left₀ h this 2
    · have h' : 0 ≤ -σ := by linarith
      have := Real.self_le_sinh_iff.2 h'
      rw [Real.sinh_neg] at this
      nlinarith
  rw [h1]; linarith

theorem exp_bump_le {lam : ℝ} (hlam : 0 < lam) (c σ : ℝ) :
    Real.exp (c * σ - lam * (Real.cosh (2 * σ) - 1)) ≤ Real.exp (c ^ 2 / (4 * lam)) * Real.exp (-lam * σ ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := two_mul_sq_le_cosh_two_mul_sub_one σ
  have : c * σ - lam * (2 * σ ^ 2) ≤ c ^ 2 / (4 * lam) + -lam * σ ^ 2 := by
    have : 0 ≤ lam * (σ - c / (2 * lam)) ^ 2 := by positivity
    have e : lam * (σ - c / (2 * lam)) ^ 2 = lam * σ ^ 2 - c * σ + c ^ 2 / (4 * lam) := by
      field_simp; ring
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h hlam.le]

theorem integrable_bump {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    Integrable (fun σ : ℝ => Real.exp (c * σ - lam * (Real.cosh (2 * σ) - 1))) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hlam).const_mul (Real.exp (c ^ 2 / (4 * lam)))) ?_ ?_
  · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ (fun σ => ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact exp_bump_le hlam c σ

theorem exp_split (c lam σ : ℝ) :
    Real.exp (c * σ - lam * Real.cosh (2 * σ)) = Real.exp (-lam) * Real.exp (c * σ - lam * (Real.cosh (2 * σ) - 1)) := by
  rw [← Real.exp_add]; congr 1; ring

theorem integrable_exp_lin_sub_mul_cosh {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    Integrable (fun σ : ℝ => Real.exp (c * σ - lam * Real.cosh (2 * σ))) := by
  have := (integrable_bump hlam c).const_mul (Real.exp (-lam))
  refine this.congr (ae_of_all _ (fun σ => ?_))
  simp only []
  rw [exp_split]

theorem integral_le_exp_neg_mul {lam₀ lam : ℝ} (h₀ : 0 < lam₀) (hle : lam₀ ≤ lam) (c : ℝ) :
    ∫ σ, Real.exp (c * σ - lam * Real.cosh (2 * σ))
      ≤ Real.exp (-lam) * ∫ σ, Real.exp (c * σ - lam₀ * (Real.cosh (2 * σ) - 1)) := by
  have hlam : 0 < lam := h₀.trans_le hle
  rw [← integral_const_mul]
  refine integral_mono (integrable_exp_lin_sub_mul_cosh hlam c) ((integrable_bump h₀ c).const_mul _) (fun σ => ?_)
  simp only []
  rw [exp_split]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _)
  have : 0 ≤ Real.cosh (2 * σ) - 1 := by linarith [Real.one_le_cosh (2 * σ)]
  nlinarith

theorem window_ge {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    2 * ρ * Real.exp (-(|c| * ρ)) * Real.exp (-(lam * Real.cosh (2 * ρ)))
      ≤ ∫ σ in {σ : ℝ | |σ| ≤ ρ}, Real.exp (c * σ - lam * Real.cosh (2 * σ)) := by
  have hset : {σ : ℝ | |σ| ≤ ρ} = Icc (-ρ) ρ := by ext v; simp [abs_le]
  rw [hset]
  have hvol : volume (Icc (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by rw [Real.volume_Icc]; congr 1; ring
  have hconst : ∫ σ in Icc (-ρ) ρ, Real.exp (-(|c| * ρ)) * Real.exp (-(lam * Real.cosh (2 * ρ)))
      = 2 * ρ * Real.exp (-(|c| * ρ)) * Real.exp (-(lam * Real.cosh (2 * ρ))) := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]; ring
  rw [← hconst]
  have hcont : Continuous (fun σ : ℝ => Real.exp (c * σ - lam * Real.cosh (2 * σ))) := Real.continuous_exp.comp (by fun_prop)
  refine setIntegral_mono_on (integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top))
    hcont.integrableOn_Icc measurableSet_Icc (fun σ hσ' => ?_)
  · have hσ : |σ| ≤ ρ := abs_le.2 hσ'
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : -(|c| * ρ) ≤ c * σ := by
      have : |c * σ| ≤ |c| * ρ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hσ (abs_nonneg c)
      linarith [neg_abs_le (c * σ)]
    have h2 : Real.cosh (2 * σ) ≤ Real.cosh (2 * ρ) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hρ]
      linarith [show |σ| ≤ ρ from hσ]
    nlinarith

theorem offWindow_le {lam₀ lam : ℝ} (h₀ : 0 < lam₀) (hle : lam₀ ≤ lam) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun σ : ℝ => Real.exp (c * σ - lam * Real.cosh (2 * σ))) {σ | δ < |σ|} ∧
    ∫ σ in {σ : ℝ | δ < |σ|}, Real.exp (c * σ - lam * Real.cosh (2 * σ))
      ≤ ((∫ σ, Real.exp (lam₀ * (-Real.cosh (2 * σ) - -Real.cosh (2 * 0) + (Real.cosh (2 * δ) - 1))) * Real.exp (|c| * |σ|))
            * Real.exp (-(-(|c| * (δ / 2)))) / (2 * (δ / 2))) * Real.exp (-(lam * (Real.cosh (2 * δ) - 1) / 2)) *
        ∫ σ in {σ : ℝ | |σ| ≤ δ}, Real.exp (c * σ - lam * Real.cosh (2 * σ)) := by
  set γ : ℝ := Real.cosh (2 * δ) - 1 with hγ
  have hγ0 : 0 < γ := by
    rw [hγ]; have := Real.one_lt_cosh.2 (show 2 * δ ≠ 0 by positivity); linarith
  have hρ : 0 < δ / 2 := by positivity

  have hshape : (fun σ : ℝ => Real.exp (lam * -Real.cosh (2 * σ)) * Real.exp (c * σ))
      = fun σ => Real.exp (c * σ - lam * Real.cosh (2 * σ)) := by
    funext σ; rw [← Real.exp_add]; congr 1; ring
  have hφm : Measurable (fun σ : ℝ => -Real.cosh (2 * σ)) := by fun_prop
  have hφmax : ∀ v : ℝ, -Real.cosh (2 * v) ≤ -Real.cosh (2 * 0) := by
    intro v; simp only [mul_zero, Real.cosh_zero]; linarith [Real.one_le_cosh (2 * v)]
  have hout : ∀ v : ℝ, δ < |v| → -Real.cosh (2 * v) ≤ -Real.cosh (2 * 0) - γ := by
    intro v hv
    simp only [mul_zero, Real.cosh_zero, hγ]
    have : Real.cosh (2 * δ) ≤ Real.cosh (2 * v) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hδ]; linarith
    linarith
  have hin : ∀ v : ℝ, |v| ≤ δ / 2 → -Real.cosh (2 * 0) - γ / 2 ≤ -Real.cosh (2 * v) := by
    intro v hv
    simp only [mul_zero, Real.cosh_zero, hγ]
    have h1 : Real.cosh (2 * v) ≤ Real.cosh δ := by
      rw [Real.cosh_le_cosh, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hδ]; linarith
    have h2 : Real.cosh δ ≤ (1 + Real.cosh (2 * δ)) / 2 := by
      have : (1 + Real.cosh (2 * δ)) / 2 = Real.cosh δ ^ 2 := by rw [Real.cosh_two_mul, Real.sinh_sq]; ring
      rw [this]; nlinarith [Real.one_le_cosh δ]
    linarith

  have hHint : Integrable (fun v : ℝ => Real.exp (lam₀ * (-Real.cosh (2 * v) - -Real.cosh (2 * 0) + γ)) * Real.exp (|c| * |v|)) := by
    have hb1 := integrable_bump h₀ |c|
    have hb2 := integrable_bump h₀ (-|c|)
    refine Integrable.mono' (((hb1.add hb2)).const_mul (Real.exp (lam₀ * γ))) (by
      exact ((Real.continuous_exp.comp (by fun_prop)).mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable) ?_
    refine ae_of_all _ (fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [mul_zero, Real.cosh_zero, Pi.add_apply]
    have e1 : Real.exp (lam₀ * (-Real.cosh (2 * v) - -1 + γ)) * Real.exp (|c| * |v|)
        = Real.exp (lam₀ * γ) * Real.exp (|c| * |v| - lam₀ * (Real.cosh (2 * v) - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rcases le_or_gt 0 v with hv | hv
    · rw [abs_of_nonneg hv]
      have : 0 ≤ Real.exp (-|c| * v - lam₀ * (Real.cosh (2 * v) - 1)) := Real.exp_nonneg _
      linarith
    · rw [abs_of_neg hv, show |c| * -v = -|c| * v by ring]
      have : 0 ≤ Real.exp (|c| * v - lam₀ * (Real.cosh (2 * v) - 1)) := Real.exp_nonneg _
      linarith
  have hHloc : IntegrableOn (fun v : ℝ => Real.exp (|c| * |v|)) {v | |v| ≤ δ} := by
    rw [show {v : ℝ | |v| ≤ δ} = Icc (-δ) δ by ext v; simp [abs_le]]
    exact (Real.continuous_exp.comp (by fun_prop)).integrableOn_Icc
  have hhH : ∀ v : ℝ, Real.exp (c * v) ≤ Real.exp (|c| * |v|) := fun v =>
    Real.exp_le_exp.2 (by rw [← abs_mul]; exact le_abs_self _)
  have hhin : ∀ v : ℝ, |v| ≤ δ / 2 → Real.exp (-(|c| * (δ / 2))) ≤ Real.exp (c * v) := by
    intro v hv
    refine Real.exp_le_exp.2 ?_
    have : |c * v| ≤ |c| * (δ / 2) := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg c)
    linarith [neg_abs_le (c * v)]
  obtain ⟨hI1, -, hmain⟩ := MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    (fun σ => -Real.cosh (2 * σ)) hφm hφmax γ δ (δ / 2) hγ0 hρ (by linarith)
    hout hin (fun v => Real.exp (|c| * |v|)) lam₀ h₀.le hHint hHloc
    (fun v => Real.exp (c * v)) (Real.continuous_exp.comp (by fun_prop)).measurable (fun v => (Real.exp_nonneg _))
    hhH (-(|c| * (δ / 2))) hhin lam hle
  rw [hshape] at hI1 hmain
  exact ⟨hI1, hmain⟩

end OcSigma

namespace OcLong

noncomputable def phi (v : ℝ) : ℝ := -(Real.exp (-2 * v) + 2 * Real.exp v)

theorem phi_zero : phi 0 = -3 := by simp [phi]; norm_num

theorem phi_zero_sub (v : ℝ) :
    phi 0 - phi v = (Real.exp v - 1) ^ 2 * (2 * Real.exp v + 1) / Real.exp v ^ 2 := by
  rw [phi_zero, phi]
  have hx : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
  rw [show Real.exp (-2 * v) = (Real.exp v ^ 2)⁻¹ by rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring]
  field_simp
  ring

theorem phi_le_phi_zero (v : ℝ) : phi v ≤ phi 0 := by
  have h := phi_zero_sub v
  have : 0 ≤ (Real.exp v - 1) ^ 2 * (2 * Real.exp v + 1) / Real.exp v ^ 2 := by positivity
  linarith

theorem phi_le_of_nonneg_le {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) : phi w ≤ phi v := by

  simp only [phi]
  set x := Real.exp v with hx
  set y := Real.exp w with hy
  have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_exp hv
  have hxy : x ≤ y := by rw [hx, hy]; exact Real.exp_le_exp.2 hvw
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have ex : Real.exp (-2 * v) = (x ^ 2)⁻¹ := by rw [hx, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have ey : Real.exp (-2 * w) = (y ^ 2)⁻¹ := by rw [hy, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [ex, ey]

  have : (x ^ 2)⁻¹ - (y ^ 2)⁻¹ ≤ 2 * y - 2 * x := by
    rw [show (x ^ 2)⁻¹ - (y ^ 2)⁻¹ = (y - x) * ((y + x) / (x ^ 2 * y ^ 2)) by field_simp; ring]
    have hfrac : (y + x) / (x ^ 2 * y ^ 2) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hx1 hx1 zero_le_one hx0.le, mul_le_mul hx1 (le_trans hx1 hxy) zero_le_one hx0.le,
        mul_le_mul (le_trans hx1 hxy) (le_trans hx1 hxy) zero_le_one hy0.le]
    nlinarith
  linarith

theorem phi_le_of_le_nonpos {v w : ℝ} (hw : w ≤ 0) (hvw : v ≤ w) : phi v ≤ phi w := by
  simp only [phi]
  set x := Real.exp v with hx
  set y := Real.exp w with hy
  have hy1 : y ≤ 1 := by rw [hy]; exact Real.exp_le_one_iff.2 hw
  have hxy : x ≤ y := by rw [hx, hy]; exact Real.exp_le_exp.2 hvw
  have hx0 : 0 < x := by rw [hx]; exact Real.exp_pos v
  have hy0 : 0 < y := by rw [hy]; exact Real.exp_pos w
  have ex : Real.exp (-2 * v) = (x ^ 2)⁻¹ := by rw [hx, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have ey : Real.exp (-2 * w) = (y ^ 2)⁻¹ := by rw [hy, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [ex, ey]

  have key : 2 * (y - x) ≤ (x ^ 2)⁻¹ - (y ^ 2)⁻¹ := by
    rw [show (x ^ 2)⁻¹ - (y ^ 2)⁻¹ = (y - x) * ((y + x) / (x ^ 2 * y ^ 2)) by field_simp; ring]
    have hfrac : 2 ≤ (y + x) / (x ^ 2 * y ^ 2) := by
      rw [le_div_iff₀ (by positivity)]

      have hx1' : x ≤ 1 := hxy.trans hy1
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hx2 : x ^ 2 ≤ 1 := by nlinarith
      have hxy2 : x * y ^ 2 ≤ 1 := by nlinarith
      have hx2y : x ^ 2 * y ≤ 1 := by nlinarith
      have h1 : x ^ 2 * y ^ 2 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hxy2 hx0.le]
      have h2 : x ^ 2 * y ^ 2 ≤ y := by nlinarith [mul_le_mul_of_nonneg_left hx2y hy0.le]
      nlinarith
    nlinarith
  linarith

theorem phi_gap {δ : ℝ} (hδ : 0 < δ) {v : ℝ} (hv : δ < |v|) :
    phi v ≤ phi 0 - min (phi 0 - phi δ) (phi 0 - phi (-δ)) := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h] at hv
    have := phi_le_of_nonneg_le hδ.le hv.le
    have := min_le_left (phi 0 - phi δ) (phi 0 - phi (-δ))
    linarith
  · rw [abs_of_neg h] at hv
    have := phi_le_of_le_nonpos (by linarith : -δ ≤ 0) (by linarith : v ≤ -δ)
    have := min_le_right (phi 0 - phi δ) (phi 0 - phi (-δ))
    linarith

theorem gap_pos {δ : ℝ} (hδ : 0 < δ) : 0 < min (phi 0 - phi δ) (phi 0 - phi (-δ)) := by
  have h1 : 0 < phi 0 - phi δ := by
    rw [phi_zero_sub]
    have : Real.exp δ - 1 ≠ 0 := by have := Real.add_one_lt_exp hδ.ne'; linarith
    positivity
  have h2 : 0 < phi 0 - phi (-δ) := by
    rw [phi_zero_sub]
    have : Real.exp (-δ) - 1 ≠ 0 := by
      have := Real.exp_lt_exp.2 (by linarith : -δ < 0); rw [Real.exp_zero] at this; linarith
    positivity
  exact lt_min h1 h2

theorem phi_zero_sub_le {v : ℝ} (hv : |v| ≤ 1) :
    phi 0 - phi v ≤ 3 * Real.exp 2 * (Real.exp |v| - 1) ^ 2 := by
  rw [phi_zero_sub]
  have hx0 : 0 < Real.exp v := Real.exp_pos v
  have hxlo : Real.exp (-1) ≤ Real.exp v := Real.exp_le_exp.2 (by linarith [neg_abs_le v, hv])
  have hxhi : Real.exp v ≤ Real.exp 1 := Real.exp_le_exp.2 (le_trans (le_abs_self v) hv)

  have h1 : (Real.exp v - 1) ^ 2 ≤ (Real.exp |v| - 1) ^ 2 := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]

      have hv1 : Real.exp v ≤ 1 := Real.exp_le_one_iff.2 h.le
      have : 1 - Real.exp v ≤ Real.exp (-v) - 1 := by
        have hprod : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-v), Real.add_one_le_exp v, Real.add_one_le_exp (-v)]
      nlinarith
  have h2 : (2 * Real.exp v + 1) / Real.exp v ^ 2 ≤ 3 * Real.exp 2 := by
    rw [div_le_iff₀ (by positivity)]
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    have hex : 1 ≤ Real.exp 1 * Real.exp v := by
      have := mul_le_mul_of_nonneg_left hxlo (Real.exp_pos 1).le; rwa [he] at this
    set x := Real.exp v with hxd
    set e := Real.exp 1 with hed
    rw [he2]
    have h3 : 1 ≤ (e * x) ^ 2 := by nlinarith
    have h4 : 2 * x ≤ 2 * e * x ^ 2 := by nlinarith
    have h5 : 2 * e * x ^ 2 ≤ 2 * (e * e) * x ^ 2 := by nlinarith [sq_nonneg x]
    nlinarith
  calc (Real.exp v - 1) ^ 2 * (2 * Real.exp v + 1) / Real.exp v ^ 2
      = (Real.exp v - 1) ^ 2 * ((2 * Real.exp v + 1) / Real.exp v ^ 2) := by ring
    _ ≤ (Real.exp |v| - 1) ^ 2 * (3 * Real.exp 2) :=
        mul_le_mul h1 h2 (by positivity) (sq_nonneg _)
    _ = 3 * Real.exp 2 * (Real.exp |v| - 1) ^ 2 := by ring

end OcLong

namespace OcShear

noncomputable def sStar (b u : ℝ) : ℝ := (1 / 4) * Real.log ((1 + Real.exp (2 * u)) / b)

noncomputable def lam (b u : ℝ) : ℝ := 2 * Real.pi * Real.sqrt (b * (1 + Real.exp (2 * u)))

theorem lam_pos {b : ℝ} (hb : 0 < b) (u : ℝ) : 0 < lam b u := by
  unfold lam; positivity

theorem two_pi_sqrt_le_lam {b : ℝ} (hb : 0 < b) (u : ℝ) : 2 * Real.pi * Real.sqrt b ≤ lam b u := by
  unfold lam
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  nlinarith [Real.exp_pos (2 * u)]

theorem exp_four_sStar {b : ℝ} (hb : 0 < b) (u : ℝ) : Real.exp (4 * sStar b u) = (1 + Real.exp (2 * u)) / b := by
  unfold sStar
  rw [show 4 * (1 / 4 * Real.log ((1 + Real.exp (2 * u)) / b)) = Real.log ((1 + Real.exp (2 * u)) / b) by ring,
    Real.exp_log (by positivity)]

theorem exp_two_sStar {b : ℝ} (hb : 0 < b) (u : ℝ) : Real.exp (2 * sStar b u) = Real.sqrt ((1 + Real.exp (2 * u)) / b) := by
  have h := exp_four_sStar hb u
  have h2 : Real.exp (2 * sStar b u) ^ 2 = (1 + Real.exp (2 * u)) / b := by
    rw [← Real.exp_nat_mul]; push_cast; rw [show (2:ℝ) * (2 * sStar b u) = 4 * sStar b u by ring, h]
  rw [← Real.sqrt_sq (Real.exp_pos _).le, h2]

theorem quad_eq_lam_cosh {b : ℝ} (hb : 0 < b) (u s : ℝ) :
    Real.pi * ((1 + Real.exp (2 * u)) * Real.exp (-(2 * s)) + b * Real.exp (2 * s))
      = lam b u * Real.cosh (2 * (s - sStar b u)) := by
  rw [Real.cosh_eq, lam]
  set A : ℝ := 1 + Real.exp (2 * u) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hE := exp_two_sStar hb u
  rw [← hA] at hE
  have hE' : Real.exp (2 * sStar b u) = Real.sqrt A / Real.sqrt b := by rw [hE, Real.sqrt_div hA0.le]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0

  have e1 : Real.exp (2 * (s - sStar b u)) = Real.exp (2 * s) * Real.sqrt b / Real.sqrt A := by
    rw [show 2 * (s - sStar b u) = 2 * s - 2 * sStar b u by ring, Real.exp_sub, hE']
    field_simp
  have e2 : Real.exp (-(2 * (s - sStar b u))) = Real.exp (-(2 * s)) * Real.sqrt A / Real.sqrt b := by
    rw [show -(2 * (s - sStar b u)) = 2 * sStar b u - 2 * s by ring, Real.exp_sub, hE', Real.exp_neg]
    field_simp
  rw [e1, e2, Real.sqrt_mul' _ hA0.le]
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0.le
  field_simp
  nlinarith [hbb, hAA, Real.exp_pos (2 * s), Real.exp_pos (-(2*s))]

open MeasureTheory Set

theorem lintegral_Ioi_eq_lintegral_exp (G : ℝ → ENNReal) :
    ∫⁻ w in Ioi (0:ℝ), G w = ∫⁻ s, G (Real.exp s) * ENNReal.ofReal (Real.exp s) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp) (s := univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr (fun s => ?_)
  rw [abs_of_pos (Real.exp_pos s), mul_comm]

theorem lintegral_Ioi_Ioi_eq_shear (b : ℝ) (F : ℝ → ℝ → ENNReal) (hF : Measurable (Function.uncurry F)) :
    ∫⁻ w in Ioi (0:ℝ), ∫⁻ r in Ioi (0:ℝ), F w r
      = ∫⁻ u, ∫⁻ σ, F (Real.exp (σ + sStar b u)) (Real.exp (u - σ - sStar b u)) * ENNReal.ofReal (Real.exp u) := by

  have h1 : ∀ w, ∫⁻ r in Ioi (0:ℝ), F w r = ∫⁻ t, F w (Real.exp t) * ENNReal.ofReal (Real.exp t) :=
    fun w => lintegral_Ioi_eq_lintegral_exp (F w)
  simp_rw [h1]
  rw [lintegral_Ioi_eq_lintegral_exp]

  have hmeas2 : Measurable (fun p : ℝ × ℝ => F (Real.exp p.1) (Real.exp p.2) * ENNReal.ofReal (Real.exp p.2) * ENNReal.ofReal (Real.exp p.1)) := by
    have : Measurable (fun p : ℝ × ℝ => F (Real.exp p.1) (Real.exp p.2)) :=
      hF.comp ((Real.measurable_exp.comp measurable_fst).prodMk (Real.measurable_exp.comp measurable_snd))
    exact (this.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_fst))
  have step1 : (∫⁻ s, (∫⁻ t, F (Real.exp s) (Real.exp t) * ENNReal.ofReal (Real.exp t)) * ENNReal.ofReal (Real.exp s))
      = ∫⁻ s, ∫⁻ t, F (Real.exp s) (Real.exp t) * ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp s) := by
    refine lintegral_congr (fun s => ?_)
    rw [← lintegral_mul_const _ ?_]
    exact ((hF.comp (measurable_const.prodMk Real.measurable_exp)).mul
      (ENNReal.measurable_ofReal.comp Real.measurable_exp))
  rw [step1]

  have step2 : ∀ s, (∫⁻ t, F (Real.exp s) (Real.exp t) * ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp s))
      = ∫⁻ u, F (Real.exp s) (Real.exp (u - s)) * ENNReal.ofReal (Real.exp (u - s)) * ENNReal.ofReal (Real.exp s) := by
    intro s
    exact (lintegral_sub_right_eq_self (fun t => F (Real.exp s) (Real.exp t) * ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp s)) s).symm
  simp_rw [step2]

  have hmeas3 : Measurable (fun p : ℝ × ℝ => F (Real.exp p.1) (Real.exp (p.2 - p.1)) * ENNReal.ofReal (Real.exp (p.2 - p.1)) * ENNReal.ofReal (Real.exp p.1)) := by
    have hsub : Measurable (fun p : ℝ × ℝ => p.2 - p.1) := measurable_snd.sub measurable_fst
    have : Measurable (fun p : ℝ × ℝ => F (Real.exp p.1) (Real.exp (p.2 - p.1))) :=
      hF.comp ((Real.measurable_exp.comp measurable_fst).prodMk (Real.measurable_exp.comp hsub))
    exact (this.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hsub))).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_fst))
  rw [lintegral_lintegral_swap hmeas3.aemeasurable]

  refine lintegral_congr (fun u => ?_)
  rw [← lintegral_add_right_eq_self (fun s => F (Real.exp s) (Real.exp (u - s)) * ENNReal.ofReal (Real.exp (u - s)) * ENNReal.ofReal (Real.exp s)) (sStar b u)]
  refine lintegral_congr (fun σ => ?_)
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2 <;> ring_nf

end OcShear

namespace Ws1
namespace ConcP4

theorem setIntegral_setIntegral_eq_toReal {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (h0 : ∀ w r, 0 ≤ f w r) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : ∫⁻ w in A, ∫⁻ r in B, ENNReal.ofReal (f w r) ≠ ⊤) :
    (∫ w in A, ∫ r in B, f w r) = (∫⁻ w in A, ∫⁻ r in B, ENNReal.ofReal (f w r)).toReal := by
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (f z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hf
  have hL : Measurable (fun w : ℝ => ∫⁻ r in B, ENNReal.ofReal (f w r)) := by
    have := Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ).restrict B) hF
    simpa using this
  have hinner : ∀ w : ℝ, (∫ r in B, f w r) = (∫⁻ r in B, ENNReal.ofReal (f w r)).toReal := by
    intro w
    have hmeas : Measurable (fun r : ℝ => f w r) := hf.comp (measurable_const.prodMk measurable_id)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun r => h0 w r))
      hmeas.aestronglyMeasurable]
  have hae : ∀ᵐ w ∂((volume : Measure ℝ).restrict A), (∫⁻ r in B, ENNReal.ofReal (f w r)) < ⊤ :=
    ae_lt_top hL hfin
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict A] fun w => ∫ r in B, f w r :=
    Filter.Eventually.of_forall (fun w => integral_nonneg (fun r => h0 w r))
  have hmeas2 : AEStronglyMeasurable (fun w => ∫ r in B, f w r) ((volume : Measure ℝ).restrict A) := by
    have : Measurable (fun w => (∫⁻ r in B, ENNReal.ofReal (f w r)).toReal) :=
      ENNReal.measurable_toReal.comp hL
    have heq : (fun w => ∫ r in B, f w r) = (fun w => (∫⁻ r in B, ENNReal.ofReal (f w r)).toReal) := by
      funext w; exact hinner w
    rw [heq]; exact this.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas2]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hae] with w hw
  rw [hinner w, ENNReal.ofReal_toReal hw.ne]

theorem mul_setIntegral_setIntegral_le {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (h0 : ∀ w r, 0 ≤ f w r) (c : NNReal) {A B A' B' : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hA' : MeasurableSet A') (hB' : MeasurableSet B')
    (hfin : ∫⁻ w in A, ∫⁻ r in B, ENNReal.ofReal (f w r) ≠ ⊤)
    (hfin' : ∫⁻ w in A', ∫⁻ r in B', ENNReal.ofReal (f w r) ≠ ⊤)
    (hle : (c : ENNReal) * (∫⁻ w in A, ∫⁻ r in B, ENNReal.ofReal (f w r)) ≤
      ∫⁻ w in A', ∫⁻ r in B', ENNReal.ofReal (f w r)) :
    (c : ℝ) * (∫ w in A, ∫ r in B, f w r) ≤ ∫ w in A', ∫ r in B', f w r := by
  rw [setIntegral_setIntegral_eq_toReal hf h0 hA hB hfin,
    setIntegral_setIntegral_eq_toReal hf h0 hA' hB' hfin']
  have h := ENNReal.toReal_mono hfin' hle
  rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at h

private lemma log_one_add_exp_sub_le (u v : ℝ) (huv : v ≤ u) :
    Real.log (1 + Real.exp (2 * u)) - Real.log (1 + Real.exp (2 * v)) ≤ 2 * (u - v) := by
  have hv : 0 < 1 + Real.exp (2 * v) := by positivity
  have hu : 0 < 1 + Real.exp (2 * u) := by positivity
  rw [← Real.log_div hu.ne' hv.ne']
  have hkey : (1 + Real.exp (2 * u)) / (1 + Real.exp (2 * v)) ≤ Real.exp (2 * (u - v)) := by
    rw [div_le_iff₀ hv]
    have h1 : (1 : ℝ) ≤ Real.exp (2 * (u - v)) := Real.one_le_exp (by linarith)
    have h2 : Real.exp (2 * (u - v)) * Real.exp (2 * v) = Real.exp (2 * u) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (2 * v), h1, h2]
  calc Real.log ((1 + Real.exp (2 * u)) / (1 + Real.exp (2 * v)))
      ≤ Real.log (Real.exp (2 * (u - v))) := Real.log_le_log (by positivity) hkey
    _ = 2 * (u - v) := Real.log_exp _

private lemma log_one_add_exp_mono (u v : ℝ) (huv : v ≤ u) :
    Real.log (1 + Real.exp (2 * v)) ≤ Real.log (1 + Real.exp (2 * u)) := by
  apply Real.log_le_log (by positivity)
  have : Real.exp (2 * v) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  linarith

private lemma abs_log_one_add_exp_sub_le (u v : ℝ) :
    |Real.log (1 + Real.exp (2 * u)) - Real.log (1 + Real.exp (2 * v))| ≤ 2 * |u - v| := by
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (by linarith [log_one_add_exp_mono u v h]), abs_of_nonneg (by linarith)]
    exact log_one_add_exp_sub_le u v h
  · rw [abs_of_nonpos (by linarith [log_one_add_exp_mono v u h]), abs_of_nonpos (by linarith)]
    have := log_one_add_exp_sub_le v u h
    linarith

theorem abs_sStar_sub_le (b : ℝ) (hb : 0 < b) (u v : ℝ) :
    |(1/4) * Real.log ((1 + Real.exp (2*u)) / b) - (1/4) * Real.log ((1 + Real.exp (2*v)) / b)|
      ≤ (1/2) * |u - v| := by
  have hu : 0 < 1 + Real.exp (2 * u) := by positivity
  have hv : 0 < 1 + Real.exp (2 * v) := by positivity
  rw [Real.log_div hu.ne' hb.ne', Real.log_div hv.ne' hb.ne']
  have h := abs_log_one_add_exp_sub_le u v
  have : (1/4) * (Real.log (1 + Real.exp (2 * u)) - Real.log b) -
      (1/4) * (Real.log (1 + Real.exp (2 * v)) - Real.log b) =
      (1/4) * (Real.log (1 + Real.exp (2 * u)) - Real.log (1 + Real.exp (2 * v))) := by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
  linarith

theorem mem_Icc_exp_of_shearBox (b : ℝ) (hb : 0 < b) (u₀ δ₁ : ℝ) (hδ₁ : 0 ≤ δ₁) (u σ : ℝ)
    (hu : |u - u₀| ≤ δ₁) (hσ : |σ| ≤ δ₁) :
    let S := fun x : ℝ => (1/4) * Real.log ((1 + Real.exp (2*x)) / b)
    Real.exp (σ + S u) ∈ Set.Icc (Real.exp (S u₀ - (5/2) * δ₁)) (Real.exp (S u₀ + (5/2) * δ₁)) ∧
    Real.exp (u - (σ + S u)) ∈
      Set.Icc (Real.exp ((u₀ - S u₀) - (5/2) * δ₁)) (Real.exp ((u₀ - S u₀) + (5/2) * δ₁)) := by
  intro S
  have hS : |S u - S u₀| ≤ (1/2) * |u - u₀| := abs_sStar_sub_le b hb u u₀
  have hS' : |S u - S u₀| ≤ (1/2) * δ₁ := hS.trans (by linarith)
  have h1 := abs_le.mp hS'
  have h2 := abs_le.mp hu
  have h3 := abs_le.mp hσ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> apply Real.exp_le_exp.mpr <;> linarith

end Ws1.ConcP4

namespace OcConc

noncomputable def T (a α β y w r : ℝ) : ℝ :=
  (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))

noncomputable def S (a u : ℝ) : ℝ := (1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)

noncomputable def lam (a u : ℝ) : ℝ := 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u)))

noncomputable def E (a α β y u : ℝ) : ℝ := -y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u + (α - β) * S a u

noncomputable def Ψ (a α β y u σ : ℝ) : ℝ := E a α β y u + (α - β) * σ - lam a u * Real.cosh (2 * σ)

theorem T_nonneg (a α β y : ℝ) {w r : ℝ} (hw : 0 < w) (hr : 0 < r) : 0 ≤ T a α β y w r := by
  unfold T
  have : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg this.le _) (Real.rpow_nonneg hw.le _)) (Real.rpow_nonneg hr.le _)) (Real.exp_nonneg _)

theorem quad_eq (a : ℝ) (ha : a ≠ 0) (u s : ℝ) :
    Real.pi * ((1 + Real.exp (2 * u)) * Real.exp (-(2 * s)) + a ^ 2 * Real.exp (2 * s))
      = lam a u * Real.cosh (2 * (s - S a u)) := by
  have hb : 0 < a ^ 2 := by positivity
  rw [Real.cosh_eq, lam, S]
  set A : ℝ := 1 + Real.exp (2 * u) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hE4 : Real.exp (4 * ((1 / 4) * Real.log (A / a ^ 2))) = A / a ^ 2 := by
    rw [show 4 * ((1 / 4) * Real.log (A / a ^ 2)) = Real.log (A / a ^ 2) by ring, Real.exp_log (by positivity)]
  have hE2 : Real.exp (2 * ((1 / 4) * Real.log (A / a ^ 2))) = Real.sqrt A / Real.sqrt (a ^ 2) := by
    have h2 : Real.exp (2 * ((1 / 4) * Real.log (A / a ^ 2))) ^ 2 = A / a ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast
      rw [show (2:ℝ) * (2 * ((1 / 4) * Real.log (A / a ^ 2))) = 4 * ((1 / 4) * Real.log (A / a ^ 2)) by ring, hE4]
    rw [← Real.sqrt_sq (Real.exp_pos _).le, h2, Real.sqrt_div hA0.le]
  have hsb : 0 < Real.sqrt (a ^ 2) := Real.sqrt_pos.2 hb
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  have e1 : Real.exp (2 * (s - (1 / 4) * Real.log (A / a ^ 2))) = Real.exp (2 * s) * Real.sqrt (a ^ 2) / Real.sqrt A := by
    rw [show 2 * (s - (1 / 4) * Real.log (A / a ^ 2)) = 2 * s - 2 * ((1 / 4) * Real.log (A / a ^ 2)) by ring, Real.exp_sub, hE2]
    field_simp
  have e2 : Real.exp (-(2 * (s - (1 / 4) * Real.log (A / a ^ 2)))) = Real.exp (-(2 * s)) * Real.sqrt A / Real.sqrt (a ^ 2) := by
    rw [show -(2 * (s - (1 / 4) * Real.log (A / a ^ 2))) = 2 * ((1 / 4) * Real.log (A / a ^ 2)) - 2 * s by ring, Real.exp_sub, hE2, Real.exp_neg]
    field_simp
  rw [e1, e2, Real.sqrt_mul' _ hA0.le]
  have hbb : Real.sqrt (a ^ 2) * Real.sqrt (a ^ 2) = a ^ 2 := Real.mul_self_sqrt hb.le
  have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0.le
  field_simp
  nlinarith [hbb, hAA, Real.exp_pos (2 * s), Real.exp_pos (-(2*s))]

theorem T_shear (a : ℝ) (ha : a ≠ 0) (α β y u σ : ℝ) :
    T a α β y (Real.exp (σ + S a u)) (Real.exp (u - σ - S a u)) * Real.exp u = Real.exp (Ψ a α β y u σ) := by
  set s : ℝ := σ + S a u with hs
  have ht : u - σ - S a u = u - s := by rw [hs]; ring
  rw [ht]
  unfold T Ψ E
  have hw : 0 < Real.exp s := Real.exp_pos s
  have hr : 0 < Real.exp (u - s) := Real.exp_pos _

  have hwr : Real.exp s * Real.exp (u - s) = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have hbase : 1 + ((Real.exp s * Real.exp (u - s)) ^ 2)⁻¹ = 1 + Real.exp (-2 * u) := by
    rw [hwr, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; congr 1; push_cast; ring
  have hbase_pos : 0 < 1 + Real.exp (-2 * u) := by positivity
  rw [hbase, Real.rpow_def_of_pos hbase_pos, ← Real.exp_mul, ← Real.exp_mul]

  have hquad : Real.pi * (Real.exp (u - s) ^ 2 + (Real.exp s ^ 2)⁻¹ + a ^ 2 * Real.exp s ^ 2)
      = lam a u * Real.cosh (2 * σ) := by
    have := quad_eq a ha u s
    rw [show s - S a u = σ by rw [hs]; ring] at this
    rw [← this]
    congr 1
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg]; push_cast
    rw [show (2:ℝ) * (u - s) = 2 * u + -(2 * s) by ring, Real.exp_add]
    ring
  rw [hquad]
  simp only [← Real.exp_add, mul_comm (Real.log _) (-y)]
  congr 1
  rw [hs]; ring

theorem lam_pos (a : ℝ) (ha : a ≠ 0) (u : ℝ) : 0 < lam a u := by
  unfold lam; have : 0 < a ^ 2 := by positivity
  positivity

theorem two_pi_abs_le_lam (a : ℝ) (ha : a ≠ 0) (u : ℝ) : 2 * Real.pi * |a| ≤ lam a u := by
  unfold lam
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq_eq_abs]
  have h1 : 1 ≤ Real.sqrt (1 + Real.exp (2 * u)) := by
    rw [Real.le_sqrt' one_pos]; nlinarith [Real.exp_pos (2 * u)]
  have : 0 ≤ 2 * Real.pi * |a| := by positivity
  nlinarith

theorem two_pi_abs_exp_le_lam (a : ℝ) (ha : a ≠ 0) (u : ℝ) : 2 * Real.pi * |a| * Real.exp u ≤ lam a u := by
  unfold lam
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq_eq_abs]
  have h1 : Real.exp u ≤ Real.sqrt (1 + Real.exp (2 * u)) := by
    rw [show Real.exp u = Real.sqrt (Real.exp (2 * u)) by
      rw [show (2:ℝ) * u = u + u by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos u).le]]
    exact Real.sqrt_le_sqrt (by linarith)
  have : 0 ≤ 2 * Real.pi * |a| := by positivity
  nlinarith

theorem lam_le (a : ℝ) (ha : a ≠ 0) (u : ℝ) : lam a u ≤ 2 * Real.pi * |a| * Real.exp u + Real.pi * |a| * Real.exp (-u) := by
  unfold lam
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq_eq_abs]
  have h1 : Real.sqrt (1 + Real.exp (2 * u)) ≤ Real.exp u + Real.exp (-u) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have h2u : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (-u), Real.exp_pos u]
  have : 0 ≤ 2 * Real.pi * |a| := by positivity
  nlinarith [Real.exp_pos (-u)]

noncomputable def Zfull (a α β u : ℝ) : ℝ := ∫ σ, Real.exp ((α - β) * σ - lam a u * Real.cosh (2 * σ))
noncomputable def Zin (a α β δ₁ u : ℝ) : ℝ := ∫ σ in {σ : ℝ | |σ| ≤ δ₁}, Real.exp ((α - β) * σ - lam a u * Real.cosh (2 * σ))
noncomputable def Zout (a α β δ₁ u : ℝ) : ℝ := ∫ σ in {σ : ℝ | δ₁ < |σ|}, Real.exp ((α - β) * σ - lam a u * Real.cosh (2 * σ))

theorem Zfull_eq_add (a : ℝ) (ha : a ≠ 0) (α β δ₁ u : ℝ) : Zfull a α β u = Zin a α β δ₁ u + Zout a α β δ₁ u := by
  unfold Zfull Zin Zout
  have hI := OcSigma.integrable_exp_lin_sub_mul_cosh (lam_pos a ha u) (α - β)
  have hS : MeasurableSet {σ : ℝ | |σ| ≤ δ₁} := measurableSet_le continuous_abs.measurable measurable_const
  rw [← integral_add_compl hS hI]
  congr 1
  rw [show {σ : ℝ | |σ| ≤ δ₁}ᶜ = {σ : ℝ | δ₁ < |σ|} by ext σ; simp [not_le]]

theorem Zin_nonneg (a α β δ₁ u : ℝ) : 0 ≤ Zin a α β δ₁ u := by
  unfold Zin; exact integral_nonneg (fun σ => (Real.exp_nonneg _))

theorem Zout_nonneg (a α β δ₁ u : ℝ) : 0 ≤ Zout a α β δ₁ u := by
  unfold Zout; exact integral_nonneg (fun σ => (Real.exp_nonneg _))

theorem Zfull_pos (a : ℝ) (ha : a ≠ 0) (α β u : ℝ) : 0 < Zfull a α β u := by
  have h := OcSigma.window_ge (lam_pos a ha u).le (α - β) (zero_lt_one)
  have h2 : Zin a α β 1 u ≤ Zfull a α β u := by
    rw [Zfull_eq_add a ha α β 1 u]; linarith [Zout_nonneg a α β 1 u]
  unfold Zin at h2
  have : 0 < 2 * (1:ℝ) * Real.exp (-(|α - β| * 1)) * Real.exp (-(lam a u * Real.cosh (2 * 1))) := by positivity
  linarith

theorem sigma_conc (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ u : ℝ, M ≤ lam a u → Zfull a α β u ≤ (1 + ε) * Zin a α β δ₁ u := by
  set lam₀ : ℝ := 2 * Real.pi * |a| with hlam₀
  have h₀ : 0 < lam₀ := by rw [hlam₀]; positivity
  set γ : ℝ := Real.cosh (2 * δ₁) - 1 with hγ
  have hγ0 : 0 < γ := by
    rw [hγ]; have := Real.one_lt_cosh.2 (show 2 * δ₁ ≠ 0 by positivity); linarith

  set K : ℝ := ((∫ σ, Real.exp (lam₀ * (-Real.cosh (2 * σ) - -Real.cosh (2 * 0) + (Real.cosh (2 * δ₁) - 1))) * Real.exp (|α - β| * |σ|))
            * Real.exp (-(-(|α - β| * (δ₁ / 2)))) / (2 * (δ₁ / 2))) with hK

  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ lam' : ℝ, M₀ ≤ lam' → K * Real.exp (-(lam' * γ / 2)) ≤ ε := by
    have ht : Filter.Tendsto (fun lam' : ℝ => K * Real.exp (-(lam' * γ / 2))) Filter.atTop (nhds (K * 0)) := by
      refine Filter.Tendsto.const_mul K ?_
      have : Filter.Tendsto (fun lam' : ℝ => -(lam' * γ / 2)) Filter.atTop Filter.atBot := by
        have : (fun lam' : ℝ => -(lam' * γ / 2)) = fun lam' => lam' * (-(γ / 2)) := by funext x; ring
        rw [this]; exact Filter.tendsto_id.atTop_mul_const_of_neg' (by linarith) |>.mono_right le_rfl
      exact Real.tendsto_exp_atBot.comp this
    rw [mul_zero] at ht
    exact (ht.eventually (Iio_mem_nhds hε)).exists_forall_of_atTop.imp fun M₀ h lam' hl => (h lam' hl).le
  refine ⟨max M₀ lam₀, fun u hu => ?_⟩
  have hle : lam₀ ≤ lam a u := (le_max_right _ _).trans hu
  obtain ⟨-, hoff⟩ := OcSigma.offWindow_le h₀ hle (α - β) hδ₁
  have hout : Zout a α β δ₁ u ≤ K * Real.exp (-(lam a u * γ / 2)) * Zin a α β δ₁ u := by
    unfold Zout Zin; rw [hK, hγ]; exact hoff
  have hKe : K * Real.exp (-(lam a u * γ / 2)) ≤ ε := hM₀ _ ((le_max_left _ _).trans hu)
  rw [Zfull_eq_add a ha α β δ₁ u]
  have hZin := Zin_nonneg a α β δ₁ u
  nlinarith

noncomputable def ustar (a y : ℝ) : ℝ := (1 / 3) * Real.log (y / (Real.pi * |a|))

theorem measurable_T (a α β y : ℝ) : Measurable (Function.uncurry (T a α β y)) := by
  unfold T Function.uncurry
  refine Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_
  · exact (measurable_const.add ((measurable_fst.mul measurable_snd).pow_const 2).inv).pow_const _
  · exact measurable_fst.pow_const _
  · exact measurable_snd.pow_const _
  · exact Real.measurable_exp.comp (by fun_prop)

theorem measurable_Ψ (a α β y : ℝ) : Measurable (fun p : ℝ × ℝ => Ψ a α β y p.1 p.2) := by
  unfold Ψ E S lam; fun_prop

theorem continuous_lam (a : ℝ) : Continuous (lam a) := by unfold lam; fun_prop
theorem continuous_S (a : ℝ) (ha : a ≠ 0) : Continuous (S a) := by
  unfold S
  refine continuous_const.mul ((Continuous.log (by fun_prop) (fun u => ?_)))
  have : 0 < a ^ 2 := by positivity
  positivity

theorem lintegral_sigma_univ (a : ℝ) (ha : a ≠ 0) (α β y u : ℝ) :
    ∫⁻ σ, ENNReal.ofReal (Real.exp (Ψ a α β y u σ)) = ENNReal.ofReal (Real.exp (E a α β y u) * Zfull a α β u) := by
  have hI := OcSigma.integrable_exp_lin_sub_mul_cosh (lam_pos a ha u) (α - β)
  unfold Zfull
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)
    (ae_of_all _ (fun σ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))]
  refine lintegral_congr (fun σ => ?_)
  congr 1
  rw [Ψ, ← Real.exp_add]; congr 1; ring

theorem lintegral_sigma_win (a : ℝ) (ha : a ≠ 0) (α β y δ₁ u : ℝ) :
    ∫⁻ σ in {σ : ℝ | |σ| ≤ δ₁}, ENNReal.ofReal (Real.exp (Ψ a α β y u σ))
      = ENNReal.ofReal (Real.exp (E a α β y u) * Zin a α β δ₁ u) := by
  have hI := (OcSigma.integrable_exp_lin_sub_mul_cosh (lam_pos a ha u) (α - β)).integrableOn (s := {σ : ℝ | |σ| ≤ δ₁})
  unfold Zin
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)
    (ae_of_all _ (fun σ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))]
  refine lintegral_congr (fun σ => ?_)
  congr 1
  rw [Ψ, ← Real.exp_add]; congr 1; ring

namespace LC

noncomputable def Lam (a y : ℝ) : ℝ := Real.pi * |a| * Real.exp (ustar a y)

theorem Lam_pos (a : ℝ) (ha : a ≠ 0) (y : ℝ) : 0 < Lam a y := by
  unfold Lam; have : 0 < |a| := abs_pos.2 ha
  positivity

theorem exp_three_ustar (a : ℝ) (ha : a ≠ 0) {y : ℝ} (hy : 0 < y) :
    Real.exp (3 * ustar a y) = y / (Real.pi * |a|) := by
  unfold ustar
  have : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  rw [show 3 * (1 / 3 * Real.log (y / (Real.pi * |a|))) = Real.log (y / (Real.pi * |a|)) by ring, Real.exp_log (by positivity)]

theorem y_mul_exp_neg_two_ustar (a : ℝ) (ha : a ≠ 0) {y : ℝ} (hy : 0 < y) :
    y * Real.exp (-2 * ustar a y) = Lam a y := by
  have h3 := exp_three_ustar a ha hy
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  unfold Lam

  have hy' : y = Real.pi * |a| * Real.exp (3 * ustar a y) := by rw [h3]; field_simp
  calc y * Real.exp (-2 * ustar a y) = Real.pi * |a| * Real.exp (3 * ustar a y) * Real.exp (-2 * ustar a y) := by rw [← hy']
    _ = Real.pi * |a| * Real.exp (ustar a y) := by rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring

theorem y_eq (a : ℝ) (ha : a ≠ 0) {y : ℝ} (hy : 0 < y) :
    y = Lam a y ^ 3 / (Real.pi * |a|) ^ 2 := by
  have h3 := exp_three_ustar a ha hy
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  unfold Lam
  rw [mul_pow, ← Real.exp_nat_mul]; push_cast; rw [h3]; field_simp

theorem le_Lam (a : ℝ) (ha : a ≠ 0) {M y : ℝ} (hM : 0 ≤ M) (hy : 0 < y) (h : M ^ 3 / (Real.pi * |a|) ^ 2 ≤ y) :
    M ≤ Lam a y := by
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hL := Lam_pos a ha y
  rw [y_eq a ha hy, div_le_div_iff_of_pos_right (by positivity)] at h
  by_contra hlt
  push Not at hlt
  have : Lam a y ^ 3 < M ^ 3 := by
    exact pow_lt_pow_left₀ hlt hL.le (by norm_num)
  linarith

theorem E_eq (a : ℝ) (ha : a ≠ 0) (α β y u : ℝ) :
    E a α β y u = -y * Real.log (1 + Real.exp (-2 * u)) + (β + 1 + (α - β) / 2) * u
      + ((α - β) / 4) * Real.log (1 + Real.exp (-2 * u)) - ((α - β) / 2) * Real.log |a| := by
  unfold E S
  have ha2 : 0 < a ^ 2 := by positivity
  have h1 : Real.log ((1 + Real.exp (2 * u)) / a ^ 2) = Real.log (1 + Real.exp (2 * u)) - 2 * Real.log |a| := by
    rw [Real.log_div (by positivity) ha2.ne', show a ^ 2 = |a| ^ 2 by rw [sq_abs], Real.log_pow]; push_cast; ring
  have h2 : Real.log (1 + Real.exp (2 * u)) = 2 * u + Real.log (1 + Real.exp (-2 * u)) := by
    have : 1 + Real.exp (2 * u) = Real.exp (2 * u) * (1 + Real.exp (-2 * u)) := by
      rw [mul_add, mul_one, ← Real.exp_add]; simp; ring
    rw [this, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  rw [h1, h2]; ring

end LC

namespace LC

theorem sub_log_one_add_bounds {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t - Real.log (1 + t) ∧ t - Real.log (1 + t) ≤ t ^ 2 := by
  have h1t : 0 < 1 + t := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos h1t; linarith
  · have h := Real.one_sub_inv_le_log_of_pos h1t
    have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
    rw [this] at h
    have : t - t / (1 + t) = t ^ 2 / (1 + t) := by field_simp; ring
    have : t ^ 2 / (1 + t) ≤ t ^ 2 := div_le_self (sq_nonneg t) (by linarith)
    linarith

theorem cosh_sub_one_le_sq {t : ℝ} (ht : |t| ≤ 1) : Real.cosh t - 1 ≤ t ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq t
  have ht2 : t ^ 2 ≤ 1 := by
    have : |t| ^ 2 ≤ 1 := by nlinarith [abs_nonneg t]
    rwa [sq_abs] at this
  have hs : |t ^ 2 / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have h2 := Real.abs_exp_sub_one_sub_id_le hs
  have h3 : Real.exp (t ^ 2 / 2) - 1 - t ^ 2 / 2 ≤ (t ^ 2 / 2) ^ 2 := le_trans (le_abs_self _) h2
  nlinarith [sq_nonneg t]

variable (a : ℝ) (ha : a ≠ 0) (α β : ℝ)

noncomputable def G (a α β y v : ℝ) : ℝ :=
  Real.exp (-y * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + (β + 1 + (α - β) / 2) * v
      + ((α - β) / 4) * Real.log (1 + Real.exp (-2 * (ustar a y + v)))) * Zfull a α β (ustar a y + v)

theorem F_eq_const_mul_G (a : ℝ) (ha : a ≠ 0) (α β y v : ℝ) :
    Real.exp (E a α β y (ustar a y + v)) * Zfull a α β (ustar a y + v)
      = Real.exp ((β + 1 + (α - β) / 2) * ustar a y - ((α - β) / 2) * Real.log |a|) * G a α β y v := by
  rw [G, E_eq a ha, ← mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem G_nonneg (a : ℝ) (ha : a ≠ 0) (α β y v : ℝ) : 0 ≤ G a α β y v :=
  mul_nonneg (Real.exp_nonneg _) (Zfull_pos a ha α β _).le

noncomputable def CZ (a α β : ℝ) : ℝ := ∫ σ, Real.exp ((α - β) * σ - (2 * Real.pi * |a|) * (Real.cosh (2 * σ) - 1))

theorem CZ_pos (a : ℝ) (ha : a ≠ 0) (α β : ℝ) : 0 < CZ a α β := by
  unfold CZ
  have h0 : 0 < 2 * Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hI := OcSigma.integrable_bump h0 (α - β)
  refine (integral_pos_iff_support_of_nonneg (fun σ => (Real.exp_nonneg _)) hI).2 ?_
  have : Function.support (fun σ : ℝ => Real.exp ((α - β) * σ - (2 * Real.pi * |a|) * (Real.cosh (2 * σ) - 1))) = univ := by
    ext σ; simp [(Real.exp_pos _).ne']
  rw [this]; simp

theorem Zfull_le (a : ℝ) (ha : a ≠ 0) (α β u : ℝ) : Zfull a α β u ≤ Real.exp (-lam a u) * CZ a α β := by
  unfold Zfull CZ
  have h0 : 0 < 2 * Real.pi * |a| := by have := abs_pos.2 ha; positivity
  exact OcSigma.integral_le_exp_neg_mul h0 (two_pi_abs_le_lam a ha u) (α - β)

theorem Zfull_ge (a : ℝ) (ha : a ≠ 0) (α β u : ℝ) {ρ' : ℝ} (hρ' : 0 < ρ') :
    2 * ρ' * Real.exp (-(|α - β| * ρ')) * Real.exp (-(lam a u * Real.cosh (2 * ρ'))) ≤ Zfull a α β u := by
  have h := OcSigma.window_ge (lam_pos a ha u).le (α - β) hρ'
  have h2 : Zin a α β ρ' u ≤ Zfull a α β u := by
    rw [Zfull_eq_add a ha α β ρ' u]; linarith [Zout_nonneg a α β ρ' u]
  unfold Zin at h2
  linarith

end LC

namespace LC

noncomputable def LamA (a : ℝ) : ℝ := max 4 (max ((Real.pi * |a|) ^ 2 * Real.exp 8) (Real.pi * |a| * Real.exp 2))

theorem x_facts (a : ℝ) (ha : a ≠ 0) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y) {v : ℝ} (hv : -2 ≤ v) :
    let x := Real.exp (-2 * (ustar a y + v))
    0 < x ∧ x ≤ 1 ∧ y * x = Lam a y * Real.exp (-2 * v) ∧ y * x ^ 2 ≤ 1 := by
  intro x
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hL := Lam_pos a ha y
  have hx0 : 0 < x := Real.exp_pos _
  have h4 : (4:ℝ) ≤ Lam a y := le_trans (le_max_left _ _) hΛ
  have h8 : (Real.pi * |a|) ^ 2 * Real.exp 8 ≤ Lam a y := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hΛ
  have h2 : Real.pi * |a| * Real.exp 2 ≤ Lam a y := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hΛ

  have heu : Real.exp (ustar a y) = Lam a y / (Real.pi * |a|) := by unfold Lam; field_simp
  have hx : x = (Real.pi * |a| / Lam a y) ^ 2 * Real.exp (-2 * v) := by
    show Real.exp (-2 * (ustar a y + v)) = _
    rw [show -2 * (ustar a y + v) = -2 * v + -(2 * ustar a y) by ring, Real.exp_add, Real.exp_neg,
      show 2 * ustar a y = ((2:ℕ):ℝ) * ustar a y by norm_num, Real.exp_nat_mul, heu]
    field_simp
  have hyx : y * x = Lam a y * Real.exp (-2 * v) := by
    have := y_mul_exp_neg_two_ustar a ha hy
    show y * Real.exp (-2 * (ustar a y + v)) = _
    rw [show -2 * (ustar a y + v) = -2 * ustar a y + -2 * v by ring, Real.exp_add, ← mul_assoc, this]
  have hev : Real.exp (-2 * v) ≤ Real.exp 4 := Real.exp_le_exp.2 (by linarith)
  refine ⟨hx0, ?_, hyx, ?_⟩
  · rw [hx]
    have : (Real.pi * |a| / Lam a y) ^ 2 * Real.exp 4 ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      have : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 2, mul_pos hpa (Real.exp_pos 2)]
    calc (Real.pi * |a| / Lam a y) ^ 2 * Real.exp (-2 * v) ≤ (Real.pi * |a| / Lam a y) ^ 2 * Real.exp 4 :=
          mul_le_mul_of_nonneg_left hev (sq_nonneg _)
      _ ≤ 1 := this
  ·
    rw [sq, ← mul_assoc, hyx, hx]
    have e8 : Real.exp (-2 * v) * Real.exp (-2 * v) ≤ Real.exp 8 := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have : Lam a y * Real.exp (-2 * v) * ((Real.pi * |a| / Lam a y) ^ 2 * Real.exp (-2 * v))
        = (Real.pi * |a|) ^ 2 / Lam a y * (Real.exp (-2 * v) * Real.exp (-2 * v)) := by
      field_simp
    rw [this]
    calc (Real.pi * |a|) ^ 2 / Lam a y * (Real.exp (-2 * v) * Real.exp (-2 * v))
        ≤ (Real.pi * |a|) ^ 2 / Lam a y * Real.exp 8 := mul_le_mul_of_nonneg_left e8 (by positivity)
      _ ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hL]; exact h8

theorem two_Lam_exp_le_lam (a : ℝ) (ha : a ≠ 0) (y v : ℝ) :
    2 * Lam a y * Real.exp v ≤ lam a (ustar a y + v) := by
  have := two_pi_abs_exp_le_lam a ha (ustar a y + v)
  unfold Lam
  rw [Real.exp_add] at this
  linarith [this]

theorem G_mul_le (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y)
    {v : ℝ} (hv : -2 ≤ v) :
    G a α β y v * Real.exp (-(Lam a y * OcLong.phi v))
      ≤ CZ a α β * Real.exp (1 + |α - β| / 4 + |β + 1 + (α - β) / 2| * |v|) := by
  obtain ⟨hx0, hx1, hyx, hyx2⟩ := x_facts a ha hy hΛ hv
  set x := Real.exp (-2 * (ustar a y + v)) with hxdef
  set κ₁ := β + 1 + (α - β) / 2 with hκ
  set c := α - β with hc
  have hZ := Zfull_le a ha α β (ustar a y + v)
  have hlam := two_Lam_exp_le_lam a ha y v
  have hCZ := (CZ_pos a ha α β).le

  have hphi : -(Lam a y * OcLong.phi v) = Lam a y * Real.exp (-2 * v) + 2 * Lam a y * Real.exp v := by
    simp only [OcLong.phi]; ring
  unfold G
  rw [hphi, mul_assoc, mul_comm (Zfull a α β _), ← mul_assoc, ← Real.exp_add]

  have hlog := sub_log_one_add_bounds hx0.le
  have hlogle : Real.log (1 + x) ≤ x := by linarith [hlog.1]
  have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hA : -y * Real.log (1 + x) + κ₁ * v + c / 4 * Real.log (1 + x) + (Lam a y * Real.exp (-2 * v) + 2 * Lam a y * Real.exp v)
      ≤ (1 + |c| / 4 + |κ₁| * |v|) + 2 * Lam a y * Real.exp v := by
    have h1 : -y * Real.log (1 + x) + Lam a y * Real.exp (-2 * v) ≤ 1 := by
      rw [← hyx]; nlinarith [hlog.2, hyx2, hy]
    have h2 : κ₁ * v ≤ |κ₁| * |v| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : c / 4 * Real.log (1 + x) ≤ |c| / 4 := by
      have : c / 4 * Real.log (1 + x) ≤ |c| / 4 * Real.log (1 + x) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self c, neg_abs_le c]) hlog0
      have : |c| / 4 * Real.log (1 + x) ≤ |c| / 4 * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    linarith
  calc Real.exp (-y * Real.log (1 + x) + κ₁ * v + c / 4 * Real.log (1 + x) + (Lam a y * Real.exp (-2 * v) + 2 * Lam a y * Real.exp v)) * Zfull a α β (ustar a y + v)
      ≤ Real.exp ((1 + |c| / 4 + |κ₁| * |v|) + 2 * Lam a y * Real.exp v) * (Real.exp (-lam a (ustar a y + v)) * CZ a α β) :=
        mul_le_mul (Real.exp_le_exp.2 hA) hZ (Zfull_pos a ha α β _).le (Real.exp_nonneg _)
    _ = CZ a α β * Real.exp ((1 + |c| / 4 + |κ₁| * |v|) + (2 * Lam a y * Real.exp v - lam a (ustar a y + v))) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ CZ a α β * Real.exp (1 + |α - β| / 4 + |β + 1 + (α - β) / 2| * |v|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCZ
        rw [hc, hκ]; linarith

end LC

namespace LC

theorem lam_le_two_Lam (a : ℝ) (ha : a ≠ 0) (y v : ℝ) :
    lam a (ustar a y + v) ≤ 2 * Lam a y * Real.exp v + Real.pi * |a| * Real.exp (-(ustar a y + v)) := by
  have := lam_le a ha (ustar a y + v)
  unfold Lam; rw [Real.exp_add] at this; linarith

theorem ridge_cost_le (a : ℝ) (ha : a ≠ 0) (y v : ℝ) (hL4 : 4 ≤ Lam a y) (hv1 : v ≤ 1) (hu0 : 0 ≤ ustar a y + v) :
    lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y))) - 2 * Lam a y * Real.exp v
      ≤ 8 * Real.exp 1 + 2 * Real.pi * |a| := by
  set Λ := Lam a y with hΛd
  have hL : 0 < Λ := by linarith
  have hsq : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hL
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hlamle := lam_le_two_Lam a ha y v
  have hlampos := lam_pos a ha (ustar a y + v)

  have ht : |2 * (1 / Real.sqrt Λ)| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    have : 2 ≤ Real.sqrt Λ := by rw [show (2:ℝ) = Real.sqrt 4 by norm_num]; exact Real.sqrt_le_sqrt hL4
    rw [mul_one_div, div_le_one hsq]; exact this
  have hcosh : Real.cosh (2 * (1 / Real.sqrt Λ)) - 1 ≤ 4 / Λ := by
    have h := cosh_sub_one_le_sq ht
    have : (2 * (1 / Real.sqrt Λ)) ^ 2 = 4 / Λ := by
      rw [mul_pow, one_div, inv_pow, Real.sq_sqrt hL.le]; norm_num; rw [div_eq_mul_inv]
    linarith
  have heu : Real.exp (-(ustar a y + v)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hev : Real.exp v ≤ Real.exp 1 := Real.exp_le_exp.2 hv1
  have hlam_up : lam a (ustar a y + v) ≤ 2 * Λ * Real.exp 1 + Real.pi * |a| := by
    have := mul_le_mul_of_nonneg_left hev (by positivity : (0:ℝ) ≤ 2 * Λ)
    have := mul_le_mul_of_nonneg_left heu hpa.le
    linarith
  have e1 : lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt Λ)) - 2 * Λ * Real.exp v
      = lam a (ustar a y + v) * (Real.cosh (2 * (1 / Real.sqrt Λ)) - 1) + (lam a (ustar a y + v) - 2 * Λ * Real.exp v) := by ring
  rw [e1]
  have hc0 : 0 ≤ Real.cosh (2 * (1 / Real.sqrt Λ)) - 1 := by linarith [Real.one_le_cosh (2 * (1 / Real.sqrt Λ))]
  have t1 : lam a (ustar a y + v) * (Real.cosh (2 * (1 / Real.sqrt Λ)) - 1) ≤ (2 * Λ * Real.exp 1 + Real.pi * |a|) * (4 / Λ) :=
    mul_le_mul hlam_up hcosh hc0 (by positivity)
  have t2 : (2 * Λ * Real.exp 1 + Real.pi * |a|) * (4 / Λ) = 8 * Real.exp 1 + 4 * (Real.pi * |a|) / Λ := by
    field_simp; ring
  have t3 : 4 * (Real.pi * |a|) / Λ ≤ Real.pi * |a| := by
    rw [div_le_iff₀ hL]; nlinarith
  have t4 : lam a (ustar a y + v) - 2 * Λ * Real.exp v ≤ Real.pi * |a| := by
    have := mul_le_mul_of_nonneg_left heu hpa.le; linarith
  linarith

theorem G_mul_ge (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y)
    (hu : 2 ≤ ustar a y) {v : ℝ} (hvabs : |v| ≤ 1) :
    (2 / Real.sqrt (Lam a y)) * Real.exp (-(|β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a|))
      ≤ G a α β y v * Real.exp (-(Lam a y * OcLong.phi v)) := by
  have hv2 : -2 ≤ v := by linarith [neg_abs_le v]
  have hv1 : v ≤ 1 := le_trans (le_abs_self v) hvabs
  obtain ⟨hx0, hx1, hyx, hyx2⟩ := x_facts a ha hy hΛ hv2
  have hL : 0 < Lam a y := Lam_pos a ha y
  have h4 : (4:ℝ) ≤ Lam a y := le_trans (le_max_left _ _) hΛ
  have hsq : 0 < Real.sqrt (Lam a y) := Real.sqrt_pos.2 hL
  have hu0 : 0 ≤ ustar a y + v := by linarith
  have hρ'pos : 0 < 1 / Real.sqrt (Lam a y) := by positivity
  have hρ'le : 1 / Real.sqrt (Lam a y) ≤ 1 := by
    rw [div_le_one hsq]; have : Real.sqrt 1 ≤ Real.sqrt (Lam a y) := Real.sqrt_le_sqrt (by linarith); simpa using this
  have hZ := Zfull_ge a ha α β (ustar a y + v) hρ'pos
  have hcost := ridge_cost_le a ha y v h4 hv1 hu0
  have hlog := sub_log_one_add_bounds hx0.le
  have hlog0 : 0 ≤ Real.log (1 + Real.exp (-2 * (ustar a y + v))) := Real.log_nonneg (by linarith)

  have hphi : -(Lam a y * OcLong.phi v) = Lam a y * Real.exp (-2 * v) + 2 * Lam a y * Real.exp v := by
    simp only [OcLong.phi]; ring
  have hG : G a α β y v * Real.exp (-(Lam a y * OcLong.phi v))
      = Real.exp (-y * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + (β + 1 + (α - β) / 2) * v
          + (α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + Lam a y * Real.exp (-2 * v))
        * (Real.exp (2 * Lam a y * Real.exp v) * Zfull a α β (ustar a y + v)) := by
    unfold G; rw [hphi]; simp only [Real.exp_add]; ring
  rw [hG]

  have hA : -(|β + 1 + (α - β) / 2| + |α - β| / 4)
      ≤ -y * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + (β + 1 + (α - β) / 2) * v
          + (α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + Lam a y * Real.exp (-2 * v) := by
    have h1 : 0 ≤ -y * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + Lam a y * Real.exp (-2 * v) := by
      rw [← hyx]; nlinarith [hlog.1, hy]
    have h2 : -|β + 1 + (α - β) / 2| ≤ (β + 1 + (α - β) / 2) * v := by
      have : |(β + 1 + (α - β) / 2) * v| ≤ |β + 1 + (α - β) / 2| * 1 := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hvabs (abs_nonneg _)
      linarith [neg_abs_le ((β + 1 + (α - β) / 2) * v)]
    have h3 : -(|α - β| / 4) ≤ (α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v))) := by
      have : |(α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v)))| ≤ |α - β| / 4 * 1 := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_nonneg hlog0]
        exact mul_le_mul_of_nonneg_left (by linarith [hlog.1]) (by positivity)
      linarith [neg_abs_le ((α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v))))]
    linarith

  have hB : (2 / Real.sqrt (Lam a y)) * Real.exp (-|α - β|) * Real.exp (-(8 * Real.exp 1 + 2 * Real.pi * |a|))
      ≤ Real.exp (2 * Lam a y * Real.exp v) * Zfull a α β (ustar a y + v) := by
    have hc1 : Real.exp (-|α - β|) ≤ Real.exp (-(|α - β| * (1 / Real.sqrt (Lam a y)))) :=
      Real.exp_le_exp.2 (by nlinarith [abs_nonneg (α - β), hρ'le])
    have step : (2 / Real.sqrt (Lam a y)) * Real.exp (-|α - β|) * Real.exp (-(8 * Real.exp 1 + 2 * Real.pi * |a|))
        ≤ Real.exp (2 * Lam a y * Real.exp v) * (2 * (1 / Real.sqrt (Lam a y)) * Real.exp (-(|α - β| * (1 / Real.sqrt (Lam a y))))
            * Real.exp (-(lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y)))))) := by
      have e : Real.exp (2 * Lam a y * Real.exp v) * (2 * (1 / Real.sqrt (Lam a y)) * Real.exp (-(|α - β| * (1 / Real.sqrt (Lam a y))))
            * Real.exp (-(lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y))))))
          = (2 / Real.sqrt (Lam a y)) * Real.exp (-(|α - β| * (1 / Real.sqrt (Lam a y))))
            * Real.exp (2 * Lam a y * Real.exp v - lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y)))) := by
        rw [show 2 * Lam a y * Real.exp v - lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y)))
          = 2 * Lam a y * Real.exp v + -(lam a (ustar a y + v) * Real.cosh (2 * (1 / Real.sqrt (Lam a y)))) by ring, Real.exp_add]
        ring
      rw [e]
      refine mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_nonneg _) (by positivity)
    exact step.trans (mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _))

  have hsplit : (2 / Real.sqrt (Lam a y)) * Real.exp (-(|β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a|))
      = Real.exp (-(|β + 1 + (α - β) / 2| + |α - β| / 4))
        * ((2 / Real.sqrt (Lam a y)) * Real.exp (-|α - β|) * Real.exp (-(8 * Real.exp 1 + 2 * Real.pi * |a|))) := by
    rw [show -(|β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a|)
      = -(|β + 1 + (α - β) / 2| + |α - β| / 4) + (-|α - β|) + (-(8 * Real.exp 1 + 2 * Real.pi * |a|)) by ring,
      Real.exp_add, Real.exp_add]; ring
  rw [hsplit]
  exact mul_le_mul (Real.exp_le_exp.2 hA) hB (by positivity) (Real.exp_nonneg _)

end LC

namespace LC

noncomputable def Gt (a α β y v : ℝ) : ℝ := Set.indicator (Set.Ici (-2 : ℝ)) (fun _ => (1:ℝ)) v * G a α β y v

theorem Gt_nonneg (a : ℝ) (ha : a ≠ 0) (α β y v : ℝ) : 0 ≤ Gt a α β y v :=
  mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (G_nonneg a ha α β y v)

theorem Gt_of_ge (a α β y : ℝ) {v : ℝ} (hv : -2 ≤ v) : Gt a α β y v = G a α β y v := by
  unfold Gt; rw [Set.indicator_of_mem (by exact hv), one_mul]

theorem Gt_of_lt (a α β y : ℝ) {v : ℝ} (hv : v < -2) : Gt a α β y v = 0 := by
  unfold Gt; rw [Set.indicator_of_notMem (by simp [hv]), zero_mul]

theorem Gt_le_G (a : ℝ) (ha : a ≠ 0) (α β y v : ℝ) : Gt a α β y v ≤ G a α β y v := by
  rcases le_or_gt (-2) v with h | h
  · rw [Gt_of_ge a α β y h]
  · rw [Gt_of_lt a α β y h]; exact G_nonneg a ha α β y v

theorem measurable_Zfull (a α β : ℝ) : Measurable (Zfull a α β) := by
  unfold Zfull
  have : Continuous (Function.uncurry (fun u σ : ℝ => Real.exp ((α - β) * σ - lam a u * Real.cosh (2 * σ)))) := by
    unfold Function.uncurry lam; fun_prop
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right this.stronglyMeasurable).measurable

theorem measurable_G (a α β y : ℝ) : Measurable (G a α β y) := by
  unfold G
  refine Measurable.mul (Real.measurable_exp.comp (by fun_prop)) ((measurable_Zfull a α β).comp (by fun_prop))

theorem measurable_Gt (a α β y : ℝ) : Measurable (Gt a α β y) := by
  unfold Gt
  exact ((measurable_const.indicator measurableSet_Ici).mul (measurable_G a α β y))

theorem trunc_exp_phi_le (κ v : ℝ) (hv : -2 ≤ v) :
    Real.exp (OcLong.phi v + |κ| * |v|) ≤ Real.exp (2 * |κ| + |κ| ^ 2 / 2) * Real.exp (-(1/2) * v ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rcases le_or_gt 0 v with h | h
  ·
    rw [abs_of_nonneg h]
    have h1 : OcLong.phi v ≤ -2 * Real.exp v := by
      simp only [OcLong.phi]; linarith [Real.exp_pos (-2 * v)]
    have h2 := Real.quadratic_le_exp_of_nonneg h
    nlinarith [sq_nonneg (v - |κ|), abs_nonneg κ]
  ·
    rw [abs_of_neg h]
    have h1 : OcLong.phi v ≤ -3 := by rw [← OcLong.phi_zero]; exact OcLong.phi_le_phi_zero v
    have : v ^ 2 ≤ 4 := by nlinarith
    nlinarith [abs_nonneg κ, sq_nonneg κ]

theorem laplace_step (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {δ' : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) :
    ∃ ρ Cst : ℝ, 0 < ρ ∧ ρ ≤ δ' ∧
      (∀ v : ℝ, |v| ≤ ρ → OcLong.phi 0 - (min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ'))) / 2 ≤ OcLong.phi v) ∧
      0 < Cst ∧ ∀ y : ℝ, 0 < y → LamA a ≤ Lam a y → 2 ≤ ustar a y →
      IntegrableOn (Gt a α β y) {v | δ' < |v|} ∧ IntegrableOn (Gt a α β y) {v | |v| ≤ δ'} ∧
      ∫ v in {v : ℝ | δ' < |v|}, Gt a α β y v
        ≤ Cst * Real.sqrt (Lam a y) * Real.exp (-(Lam a y * (min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ'))) / 2))
          * ∫ v in {v : ℝ | |v| ≤ δ'}, Gt a α β y v := by
  set γ : ℝ := min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ')) with hγ
  have hγ0 : 0 < γ := OcLong.gap_pos hδ'0

  set ρ : ℝ := min δ' (Real.log (1 + Real.sqrt (γ / (6 * Real.exp 2)))) with hρ
  have hq : 0 < Real.sqrt (γ / (6 * Real.exp 2)) := Real.sqrt_pos.2 (by positivity)
  have hρ0 : 0 < ρ := by
    rw [hρ]; refine lt_min hδ'0 (Real.log_pos (by linarith))
  have hρδ : ρ ≤ δ' := min_le_left _ _
  have hρ1 : ρ ≤ 1 := hρδ.trans hδ'1
  have hρin : ∀ v : ℝ, |v| ≤ ρ → OcLong.phi 0 - γ / 2 ≤ OcLong.phi v := by
    intro v hv
    have h1 := OcLong.phi_zero_sub_le (le_trans hv hρ1)
    have h2 : Real.exp |v| - 1 ≤ Real.sqrt (γ / (6 * Real.exp 2)) := by
      have : Real.exp |v| ≤ Real.exp ρ := Real.exp_le_exp.2 hv
      have : Real.exp ρ ≤ 1 + Real.sqrt (γ / (6 * Real.exp 2)) := by
        rw [hρ]; calc Real.exp (min δ' (Real.log (1 + Real.sqrt (γ / (6 * Real.exp 2)))))
            ≤ Real.exp (Real.log (1 + Real.sqrt (γ / (6 * Real.exp 2)))) := Real.exp_le_exp.2 (min_le_right _ _)
          _ = 1 + Real.sqrt (γ / (6 * Real.exp 2)) := Real.exp_log (by linarith)
      linarith
    have h3 : 0 ≤ Real.exp |v| - 1 := by linarith [Real.one_le_exp (abs_nonneg v)]
    have h4 : (Real.exp |v| - 1) ^ 2 ≤ γ / (6 * Real.exp 2) := by
      calc (Real.exp |v| - 1) ^ 2 ≤ Real.sqrt (γ / (6 * Real.exp 2)) ^ 2 := pow_le_pow_left₀ h3 h2 2
        _ = γ / (6 * Real.exp 2) := Real.sq_sqrt (by positivity)
    have : 3 * Real.exp 2 * (Real.exp |v| - 1) ^ 2 ≤ γ / 2 := by
      calc 3 * Real.exp 2 * (Real.exp |v| - 1) ^ 2 ≤ 3 * Real.exp 2 * (γ / (6 * Real.exp 2)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = γ / 2 := by field_simp; ring
    linarith

  set κ₁ : ℝ := β + 1 + (α - β) / 2 with hκ
  set c : ℝ := α - β with hc
  set C₀ : ℝ := |κ₁| + |c| / 4 + |c| + 8 * Real.exp 1 + 2 * Real.pi * |a| with hC₀
  set H : ℝ → ℝ := fun v => Set.indicator (Set.Ici (-2 : ℝ)) (fun _ => (1:ℝ)) v * (CZ a α β * Real.exp (1 + |c| / 4 + |κ₁| * |v|)) with hH
  set CH : ℝ := ∫ v, Real.exp (1 * (OcLong.phi v - OcLong.phi 0 + γ)) * H v with hCH
  have hCZ : 0 ≤ CZ a α β := (CZ_pos a ha α β).le
  have hHnn : ∀ v, 0 ≤ H v := fun v => by
    simp only [hH]; exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hCZ (Real.exp_nonneg _))
  have hCH0 : 0 ≤ CH := integral_nonneg (fun v => mul_nonneg (Real.exp_nonneg _) (hHnn v))
  refine ⟨ρ, (CH * (Real.exp C₀ / 2) / (2 * ρ)) + 1, hρ0, hρδ, hρin, by positivity, ?_⟩
  intro y hy hΛ hu
  have hL : 0 < Lam a y := Lam_pos a ha y
  have h4 : (4:ℝ) ≤ Lam a y := le_trans (le_max_left _ _) hΛ
  have hsq : 0 < Real.sqrt (Lam a y) := Real.sqrt_pos.2 hL

  set h : ℝ → ℝ := fun v => Gt a α β y v * Real.exp (-(Lam a y * OcLong.phi v)) with hh
  have hhm : Measurable h := (measurable_Gt a α β y).mul (Real.measurable_exp.comp (by
    have : Continuous OcLong.phi := by unfold OcLong.phi; fun_prop
    fun_prop))
  have hh0 : ∀ v, 0 ≤ h v := fun v => mul_nonneg (Gt_nonneg a ha α β y v) (Real.exp_nonneg _)
  have hhH : ∀ v, h v ≤ H v := by
    intro v
    simp only [hh, hH, Gt]
    rcases le_or_gt (-2) v with hv | hv
    · rw [Set.indicator_of_mem (show v ∈ Set.Ici (-2:ℝ) from hv), one_mul, one_mul]
      have := G_mul_le a ha α β hy hΛ hv
      rw [hc, hκ]; exact this
    · rw [Set.indicator_of_notMem (show v ∉ Set.Ici (-2:ℝ) by simp [hv]), zero_mul, zero_mul, zero_mul]
  have hhin : ∀ v, |v| ≤ ρ → Real.exp (Real.log ((2 / Real.sqrt (Lam a y)) * Real.exp (-C₀))) ≤ h v := by
    intro v hv
    have hv1 : |v| ≤ 1 := hv.trans hρ1
    have hv2 : -2 ≤ v := by linarith [neg_abs_le v]
    rw [Real.exp_log (by positivity)]
    simp only [hh]
    rw [Gt_of_ge a α β y hv2]
    have := G_mul_ge a ha α β hy hΛ hu hv1
    rw [hC₀, hc, hκ]; exact this

  have hφm : Measurable OcLong.phi := by
    have : Continuous OcLong.phi := by unfold OcLong.phi; fun_prop
    exact this.measurable
  have hHint : Integrable (fun v => Real.exp (1 * (OcLong.phi v - OcLong.phi 0 + γ)) * H v) := by
    have hmaj : Integrable (fun v : ℝ => (Real.exp (3 + γ) * CZ a α β * Real.exp (1 + |c| / 4) * Real.exp (2 * |κ₁| + |κ₁| ^ 2 / 2))
        * Real.exp (-(1/2) * v ^ 2)) := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _
    refine hmaj.mono' ?_ ?_
    · refine ((Real.measurable_exp.comp (by fun_prop)).mul ?_).aestronglyMeasurable
      simp only [hH]
      exact (measurable_const.indicator measurableSet_Ici).mul (measurable_const.mul (Real.measurable_exp.comp (by fun_prop)))
    · refine ae_of_all _ (fun v => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hHnn v))]
      simp only [hH]
      rcases le_or_gt (-2) v with hv | hv
      · rw [Set.indicator_of_mem (show v ∈ Set.Ici (-2:ℝ) from hv), OcLong.phi_zero]
        have ht := trunc_exp_phi_le κ₁ v hv
        have e : Real.exp (1 * (OcLong.phi v - -3 + γ)) * (1 * (CZ a α β * Real.exp (1 + |c| / 4 + |κ₁| * |v|)))
            = (Real.exp (3 + γ) * CZ a α β * Real.exp (1 + |c| / 4)) * Real.exp (OcLong.phi v + |κ₁| * |v|) := by
          simp only [one_mul, sub_neg_eq_add, Real.exp_add]; ring
        rw [e, mul_assoc (Real.exp (3 + γ) * CZ a α β * Real.exp (1 + |c| / 4))]
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      · rw [Set.indicator_of_notMem (show v ∉ Set.Ici (-2:ℝ) by simp [hv]), zero_mul, mul_zero]
        exact mul_nonneg (by positivity) (Real.exp_nonneg _)
  have hHloc : IntegrableOn H {v | |v| ≤ δ'} := by
    have : IntegrableOn (fun v : ℝ => CZ a α β * Real.exp (1 + |c| / 4 + |κ₁| * |v|)) (Set.Icc (-δ') δ') :=
      (Continuous.integrableOn_Icc (by fun_prop))
    rw [show {v : ℝ | |v| ≤ δ'} = Set.Icc (-δ') δ' by ext v; simp [abs_le]]
    refine this.mono' ?_ ?_
    · simp only [hH]
      exact ((measurable_const.indicator measurableSet_Ici).mul (measurable_const.mul (Real.measurable_exp.comp (by fun_prop)))).aestronglyMeasurable
    · refine ae_of_all _ (fun v => ?_)
      simp only [hH]
      rw [Real.norm_of_nonneg (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hCZ (Real.exp_nonneg _)))]
      refine mul_le_of_le_one_left (mul_nonneg hCZ (Real.exp_nonneg _)) ?_
      rcases le_or_gt (-2) v with hv | hv
      · rw [Set.indicator_of_mem (show v ∈ Set.Ici (-2:ℝ) from hv)]
      · rw [Set.indicator_of_notMem (show v ∉ Set.Ici (-2:ℝ) by simp [hv])]; norm_num

  obtain ⟨hI1, hI2, hmain⟩ := MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    OcLong.phi hφm OcLong.phi_le_phi_zero γ δ' ρ hγ0 hρ0 hρδ
    (fun v hv => OcLong.phi_gap hδ'0 hv) hρin H 1 zero_le_one hHint hHloc h hhm hh0 hhH
    (Real.log ((2 / Real.sqrt (Lam a y)) * Real.exp (-C₀))) hhin (Lam a y) (by linarith)

  have hprod : (fun v => Real.exp (Lam a y * OcLong.phi v) * h v) = Gt a α β y := by
    funext v; simp only [hh]
    rw [mul_comm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hprod] at hI1 hI2 hmain
  refine ⟨hI1, hI2, hmain.trans ?_⟩
  have hin0 : 0 ≤ ∫ v in {v : ℝ | |v| ≤ δ'}, Gt a α β y v := integral_nonneg (fun v => Gt_nonneg a ha α β y v)
  refine mul_le_mul_of_nonneg_right ?_ hin0

  rw [Real.exp_neg, Real.exp_log (by positivity)]
  have e1 : (2 / Real.sqrt (Lam a y) * Real.exp (-C₀))⁻¹ = Real.sqrt (Lam a y) * Real.exp C₀ / 2 := by
    rw [Real.exp_neg]; field_simp
  rw [show (∫ v, Real.exp (1 * (OcLong.phi v - OcLong.phi 0 + γ)) * H v) = CH from rfl, e1]
  have hexp0 : 0 ≤ Real.exp (-(Lam a y * γ / 2)) := Real.exp_nonneg _
  have : CH * (Real.sqrt (Lam a y) * Real.exp C₀ / 2) / (2 * ρ) = (CH * (Real.exp C₀ / 2) / (2 * ρ)) * Real.sqrt (Lam a y) := by
    field_simp
  rw [this]
  refine mul_le_mul_of_nonneg_right ?_ hexp0
  nlinarith [hsq.le, hCH0, Real.exp_pos C₀, hρ0]

end LC

namespace LC

theorem G_farleft_le (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y)
    (hyk : |α - β| / 2 + 2 * (|β + 1 + (α - β) / 2| + 1) ≤ y) {v : ℝ} (hv : v < -2) :
    G a α β y v ≤ CZ a α β * Real.exp (-(Lam a y * Real.exp 4 / 4))
        * Real.exp (2 * (|β + 1 + (α - β) / 2| + 1) * ustar a y) * Real.exp ((|β + 1 + (α - β) / 2| + 2) * v) := by
  set κ₁ := β + 1 + (α - β) / 2 with hκ
  set c := α - β with hc
  set k : ℝ := |κ₁| + 1 with hk
  set q : ℝ := Real.exp (-2 * ustar a y) with hq
  set x : ℝ := Real.exp (-2 * (ustar a y + v)) with hx
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hL := Lam_pos a ha y
  have hq0 : 0 < q := Real.exp_pos _
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : x = q * Real.exp (-2 * v) := by rw [hx, hq, ← Real.exp_add]; congr 1; ring
  have hyq : y * q = Lam a y := y_mul_exp_neg_two_ustar a ha hy

  have heu : Real.exp (ustar a y) = Lam a y / (Real.pi * |a|) := by unfold Lam; field_simp
  have hq' : q = (Real.pi * |a| / Lam a y) ^ 2 := by
    rw [hq, show -2 * ustar a y = -(((2:ℕ):ℝ) * ustar a y) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul, heu]
    field_simp
  have h2 : Real.pi * |a| * Real.exp 2 ≤ Lam a y := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hΛ
  have hqe : q * Real.exp 4 ≤ 1 := by
    rw [hq', show Real.exp 4 = Real.exp 2 ^ 2 by rw [← Real.exp_nat_mul]; norm_num, ← mul_pow, div_mul_eq_mul_div]
    have : Real.pi * |a| * Real.exp 2 / Lam a y ≤ 1 := by rw [div_le_one hL]; exact h2
    have : 0 ≤ Real.pi * |a| * Real.exp 2 / Lam a y := by positivity
    nlinarith

  have hxge : q * Real.exp 4 ≤ x := by
    rw [hxq]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hq0.le

  have hZ : Zfull a α β (ustar a y + v) ≤ CZ a α β := by
    have := Zfull_le a ha α β (ustar a y + v)
    have : Real.exp (-lam a (ustar a y + v)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith [lam_pos a ha (ustar a y + v)]
    nlinarith [(CZ_pos a ha α β).le]

  have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hlogx : Real.log x ≤ Real.log (1 + x) := Real.log_le_log hx0 (by linarith)
  have hlogq : Real.log x = -2 * ustar a y + -2 * v := by rw [hx, Real.log_exp]; ring

  have hA : Lam a y * Real.exp 4 / 4 ≤ y / 2 * Real.log (1 + x) := by
    have h1 : Real.log (1 + q * Real.exp 4) ≤ Real.log (1 + x) := Real.log_le_log (by positivity) (by linarith)
    have h2 : q * Real.exp 4 / 2 ≤ Real.log (1 + q * Real.exp 4) := by
      have := Real.le_log_one_add_of_nonneg (show 0 ≤ q * Real.exp 4 by positivity)

      have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + q * Real.exp 4 by positivity)
      have e : 1 - (1 + q * Real.exp 4)⁻¹ = q * Real.exp 4 / (1 + q * Real.exp 4) := by field_simp; ring
      rw [e] at h
      have : q * Real.exp 4 / 2 ≤ q * Real.exp 4 / (1 + q * Real.exp 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      linarith
    have : Lam a y * Real.exp 4 / 4 = y / 2 * (q * Real.exp 4 / 2) := by rw [← hyq]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (h2.trans h1) (by linarith)

  have hB : -y * Real.log (1 + x) + κ₁ * v + c / 4 * Real.log (1 + x)
      ≤ -(Lam a y * Real.exp 4 / 4) + 2 * k * ustar a y + (|κ₁| + 2) * v := by
    have h1 : c / 4 * Real.log (1 + x) ≤ |c| / 4 * Real.log (1 + x) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hlog0
    have hk0 : 0 ≤ k := by rw [hk]; positivity
    have h2 : -(y / 2 - |c| / 4) * Real.log (1 + x) ≤ -k * Real.log (1 + x) := by
      have : k ≤ y / 2 - |c| / 4 := by linarith
      nlinarith
    have h3 : -k * Real.log (1 + x) ≤ -k * Real.log x := by nlinarith
    have h4 : κ₁ * v + 2 * k * v ≤ (|κ₁| + 2) * v := by
      rw [hk]
      have : 0 ≤ κ₁ + |κ₁| := by have := neg_abs_le κ₁; linarith
      nlinarith
    rw [hlogq] at h3
    nlinarith
  unfold G
  calc Real.exp (-y * Real.log (1 + Real.exp (-2 * (ustar a y + v))) + (β + 1 + (α - β) / 2) * v
          + (α - β) / 4 * Real.log (1 + Real.exp (-2 * (ustar a y + v)))) * Zfull a α β (ustar a y + v)
      ≤ Real.exp (-(Lam a y * Real.exp 4 / 4) + 2 * k * ustar a y + (|κ₁| + 2) * v) * CZ a α β := by
        refine mul_le_mul (Real.exp_le_exp.2 ?_) hZ (Zfull_pos a ha α β _).le (Real.exp_nonneg _)
        rw [← hx, ← hκ, ← hc]; exact hB
    _ = CZ a α β * Real.exp (-(Lam a y * Real.exp 4 / 4)) * Real.exp (2 * (|κ₁| + 1) * ustar a y) * Real.exp ((|κ₁| + 2) * v) := by
        rw [Real.exp_add, Real.exp_add, hk]; ring

end LC

namespace LC

theorem exp_four_ge : (52:ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : (2.7:ℝ) ≤ Real.exp 1 := by linarith
  have h4 : (2.7:ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
  nlinarith

theorem gap_le_four {δ' : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) :
    min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ')) ≤ 4 := by
  refine (min_le_left _ _).trans ?_
  have h1 : OcLong.phi 1 ≤ OcLong.phi δ' := OcLong.phi_le_of_nonneg_le hδ'0.le hδ'1
  have h2 : -7 ≤ OcLong.phi 1 := by
    have he : Real.exp (-2 * (1:ℝ)) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    have h3 := Real.exp_one_lt_three
    simp only [OcLong.phi]
    linarith
  rw [OcLong.phi_zero]; linarith

theorem eventually_le_of_decay (C s b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ L : ℝ, ∀ Λ : ℝ, L ≤ Λ → C * Λ ^ s * Real.exp (-b * Λ) ≤ ε := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).const_mul C
  rw [mul_zero] at ht
  obtain ⟨L, hL⟩ := (ht.eventually (Iio_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨L, fun Λ h => by have := hL Λ h; rw [mul_assoc]; exact this.le⟩

theorem setIntegral_comp_ustar (f : ℝ → ℝ) (u₀ δ₁ : ℝ) :
    ∫ u in {u : ℝ | δ₁ < |u - u₀|}, f u = ∫ v in {v : ℝ | δ₁ < |v|}, f (u₀ + v) := by
  have hS : MeasurableSet {v : ℝ | δ₁ < |v|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hS' : MeasurableSet {u : ℝ | δ₁ < |u - u₀|} := measurableSet_lt measurable_const (by fun_prop)
  rw [← integral_indicator hS', ← integral_indicator hS]
  rw [← integral_add_left_eq_self _ u₀]
  congr 1; funext v
  simp only [Set.indicator]
  have : (u₀ + v ∈ {u : ℝ | δ₁ < |u - u₀|}) ↔ (v ∈ {v : ℝ | δ₁ < |v|}) := by simp
  by_cases h : v ∈ {v : ℝ | δ₁ < |v|}
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

theorem integral_comp_ustar (f : ℝ → ℝ) (u₀ : ℝ) : ∫ u, f u = ∫ v, f (u₀ + v) :=
  (integral_add_left_eq_self f u₀).symm

end LC

namespace LC

theorem farleft_integral (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y)
    (hyk : |α - β| / 2 + 2 * (|β + 1 + (α - β) / 2| + 1) ≤ y) :
    IntegrableOn (G a α β y) (Set.Iio (-2)) ∧
    ∫ v in Set.Iio (-2), G a α β y v ≤
      CZ a α β * Real.exp (-(Lam a y * Real.exp 4 / 4)) * Real.exp (2 * (|β + 1 + (α - β) / 2| + 1) * ustar a y) * Real.exp (-2) := by
  set κ := |β + 1 + (α - β) / 2| with hκ
  set Mfl : ℝ := CZ a α β * Real.exp (-(Lam a y * Real.exp 4 / 4)) * Real.exp (2 * (κ + 1) * ustar a y) with hMfl
  have hMfl0 : 0 ≤ Mfl := by have := (CZ_pos a ha α β).le; positivity
  have hκ0 : 0 ≤ κ := abs_nonneg _
  have hfl_pt : ∀ v : ℝ, v < -2 → G a α β y v ≤ Mfl * Real.exp ((κ + 2) * v) := fun v hv =>
    G_farleft_le a ha α β hy hΛ hyk hv
  have hSfl : MeasurableSet (Set.Iio (-2 : ℝ)) := measurableSet_Iio
  have hlin : ∀ v : ℝ, v < -2 → (κ + 2) * v ≤ v := fun v hv => by nlinarith
  have hexpI : IntegrableOn (fun v : ℝ => Real.exp v) (Set.Iio (-2)) := (integrableOn_exp_Iic (-2)).mono_set Set.Iio_subset_Iic_self
  have hexp_int : IntegrableOn (fun v : ℝ => Real.exp ((κ + 2) * v)) (Set.Iio (-2)) := by
    refine hexpI.mono' (by fun_prop : Continuous fun v : ℝ => Real.exp ((κ + 2) * v)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hSfl).2 (ae_of_all _ (fun v hv => ?_))
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.2 (hlin v hv)
  have hfl_int : IntegrableOn (G a α β y) (Set.Iio (-2)) := by
    refine (hexp_int.const_mul Mfl).mono' (measurable_G a α β y).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hSfl).2 (ae_of_all _ (fun v hv => ?_))
    rw [Real.norm_of_nonneg (G_nonneg a ha α β y v)]
    exact hfl_pt v hv
  refine ⟨hfl_int, ?_⟩
  calc ∫ v in Set.Iio (-2), G a α β y v ≤ ∫ v in Set.Iio (-2), Mfl * Real.exp ((κ + 2) * v) :=
        setIntegral_mono_on hfl_int (hexp_int.const_mul Mfl) hSfl (fun v hv => hfl_pt v hv)
    _ = Mfl * ∫ v in Set.Iio (-2), Real.exp ((κ + 2) * v) := integral_const_mul _ _
    _ ≤ Mfl * ∫ v in Set.Iic (-2), Real.exp v := by
        refine mul_le_mul_of_nonneg_left ?_ hMfl0
        calc ∫ v in Set.Iio (-2), Real.exp ((κ + 2) * v) ≤ ∫ v in Set.Iio (-2), Real.exp v :=
              setIntegral_mono_on hexp_int hexpI hSfl (fun v hv => Real.exp_le_exp.2 (hlin v hv))
          _ ≤ ∫ v in Set.Iic (-2), Real.exp v :=
              setIntegral_mono_set (integrableOn_exp_Iic (-2)) (ae_of_all _ (fun v => (Real.exp_nonneg v))) (ae_of_all _ Set.Iio_subset_Iic_self)
    _ = Mfl * Real.exp (-2) := by rw [integral_exp_Iic]

theorem window_lb (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (hΛ : LamA a ≤ Lam a y) (hu : 2 ≤ ustar a y)
    {ρ δ' g : ℝ} (hρ0 : 0 < ρ) (hρδ : ρ ≤ δ') (hδ'1 : δ' ≤ 1)
    (hρin : ∀ v : ℝ, |v| ≤ ρ → OcLong.phi 0 - g / 2 ≤ OcLong.phi v)
    (hIwin : IntegrableOn (G a α β y) {v : ℝ | |v| ≤ δ'}) :
    (2 * ρ * (2 * Real.exp (-(|β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a|))))
        * (Real.sqrt (Lam a y))⁻¹ * Real.exp (Lam a y * (OcLong.phi 0 - g / 2))
      ≤ ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v := by
  set C₀ := |β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a| with hC₀
  have hL := Lam_pos a ha y
  have hsq : 0 < Real.sqrt (Lam a y) := Real.sqrt_pos.2 hL
  have hSρ : MeasurableSet {v : ℝ | |v| ≤ ρ} := measurableSet_le continuous_abs.measurable measurable_const
  have hρsub : {v : ℝ | |v| ≤ ρ} ⊆ {v : ℝ | |v| ≤ δ'} := fun v hv => le_trans hv hρδ
  have hvol : volume {v : ℝ | |v| ≤ ρ} = ENNReal.ofReal (2 * ρ) := by
    rw [show {v : ℝ | |v| ≤ ρ} = Set.Icc (-ρ) ρ by ext v; simp [abs_le], Real.volume_Icc]; congr 1; ring
  have hpt : ∀ v ∈ {v : ℝ | |v| ≤ ρ},
      (2 / Real.sqrt (Lam a y)) * Real.exp (-C₀) * Real.exp (Lam a y * (OcLong.phi 0 - g / 2)) ≤ G a α β y v := by
    intro v hv
    have hv' : |v| ≤ ρ := hv
    have hge := G_mul_ge a ha α β hy hΛ hu (hv'.trans (hρδ.trans hδ'1))
    have hφ := hρin v hv'
    have e : G a α β y v = (G a α β y v * Real.exp (-(Lam a y * OcLong.phi v))) * Real.exp (Lam a y * OcLong.phi v) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [e]
    refine mul_le_mul hge (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _) (le_trans (by positivity) hge)
    nlinarith [hL.le, hφ]
  calc (2 * ρ * (2 * Real.exp (-C₀))) * (Real.sqrt (Lam a y))⁻¹ * Real.exp (Lam a y * (OcLong.phi 0 - g / 2))
      = ∫ v in {v : ℝ | |v| ≤ ρ}, (2 / Real.sqrt (Lam a y)) * Real.exp (-C₀) * Real.exp (Lam a y * (OcLong.phi 0 - g / 2)) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
        field_simp
    _ ≤ ∫ v in {v : ℝ | |v| ≤ ρ}, G a α β y v :=
        setIntegral_mono_on (integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top)) (hIwin.mono_set hρsub) hSρ hpt
    _ ≤ ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v :=
        setIntegral_mono_set hIwin (ae_of_all _ (fun v => G_nonneg a ha α β y v)) (ae_of_all _ hρsub)

theorem farleft_identity (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {y : ℝ} (hy : 0 < y) (k W g : ℝ) (hW : W ≠ 0) :
    CZ a α β * Real.exp (-(Lam a y * Real.exp 4 / 4)) * Real.exp (2 * k * ustar a y) * Real.exp (-2)
      = (CZ a α β * Real.exp (-2) * (Real.pi * |a|) ^ (-(2 * k)) / W * (Lam a y) ^ (2 * k + 1 / 2)
          * Real.exp (-(Real.exp 4 / 4 - 3 - g / 2) * Lam a y))
        * (W * (Real.sqrt (Lam a y))⁻¹ * Real.exp (Lam a y * (OcLong.phi 0 - g / 2))) := by
  have hL := Lam_pos a ha y
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have heu : Real.exp (ustar a y) = Lam a y / (Real.pi * |a|) := by unfold Lam; field_simp
  rw [OcLong.phi_zero, Real.sqrt_eq_rpow, show 2 * k * ustar a y = ustar a y * (2 * k) by ring, Real.exp_mul, heu,
    Real.div_rpow hL.le hpa.le, Real.rpow_neg hpa.le]
  have hp2k : (Real.pi * |a|) ^ (2 * k) ≠ 0 := (Real.rpow_pos_of_pos hpa _).ne'
  have hH0 : (Lam a y) ^ ((1:ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hexp : Real.exp (-(Lam a y * Real.exp 4 / 4)) = Real.exp (-(Real.exp 4 / 4 - 3 - g / 2) * Lam a y) * Real.exp (Lam a y * (-3 - g / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, Real.rpow_add hL (2 * k) (1 / 2)]
  generalize (Lam a y) ^ (2 * k) = P at *
  generalize (Lam a y) ^ ((1:ℝ) / 2) = Hh at *
  generalize (Real.pi * |a|) ^ (2 * k) = Q at *
  field_simp

end LC

namespace LC

theorem long_conc_G (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      Integrable (G a α β y) ∧
      ∫ v in {v : ℝ | δ₁ < |v|}, G a α β y v ≤ ε * ∫ v, G a α β y v := by
  set δ' : ℝ := min δ₁ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ₁ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ₁ := min_le_left _ _
  obtain ⟨ρ, Cst, hρ0, hρδ, hρin, hCst, hstep⟩ := laplace_step a ha α β hδ'0 hδ'1
  set γ : ℝ := min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ')) with hγ
  have hγ0 : 0 < γ := OcLong.gap_pos hδ'0
  have hγ4 : γ ≤ 4 := gap_le_four hδ'0 hδ'1
  set κ : ℝ := |β + 1 + (α - β) / 2| with hκ
  set k : ℝ := κ + 1 with hk
  set C₀ : ℝ := |β + 1 + (α - β) / 2| + |α - β| / 4 + |α - β| + 8 * Real.exp 1 + 2 * Real.pi * |a| with hC₀
  have hpa : 0 < Real.pi * |a| := by have := abs_pos.2 ha; positivity
  have hCZ := CZ_pos a ha α β
  obtain ⟨L₁, hL₁⟩ := eventually_le_of_decay Cst (1 / 2) (γ / 2) (ε / 2) (by positivity) (by positivity)
  set W : ℝ := 2 * ρ * (2 * Real.exp (-C₀)) with hW
  have hW0 : 0 < W := by positivity
  set D : ℝ := CZ a α β * Real.exp (-2) * (Real.pi * |a|) ^ (-(2 * k)) with hD
  set b : ℝ := Real.exp 4 / 4 - 3 - γ / 2 with hb
  have hb0 : 0 < b := by have := exp_four_ge; rw [hb]; linarith
  obtain ⟨L₂, hL₂⟩ := eventually_le_of_decay (D / W) (2 * k + 1 / 2) b (ε / 2) hb0 (by positivity)
  set M : ℝ := max (LamA a) (max (max L₁ 0) (max L₂ 0)) with hM
  have hM0 : 0 ≤ M := le_trans (le_trans (by norm_num) (le_max_left (4:ℝ) _)) (le_max_left _ _)
  refine ⟨max (max 1 (M ^ 3 / (Real.pi * |a|) ^ 2)) (max (Real.pi * |a| * Real.exp 6) (|α - β| / 2 + 2 * k)), fun y hyR => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hyR)
  have hy : 0 < y := by linarith
  have hyM : M ^ 3 / (Real.pi * |a|) ^ 2 ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hyR)
  have hy6 : Real.pi * |a| * Real.exp 6 ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hyR)
  have hyk : |α - β| / 2 + 2 * k ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hyR)
  have hML : M ≤ Lam a y := le_Lam a ha hM0 hy hyM
  have hΛ : LamA a ≤ Lam a y := le_trans (le_max_left _ _) hML
  have hΛ1 : L₁ ≤ Lam a y := le_trans (le_trans (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))) hML
  have hΛ2 : L₂ ≤ Lam a y := le_trans (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))) hML
  have hL := Lam_pos a ha y
  have hu : 2 ≤ ustar a y := by
    have h3 := exp_three_ustar a ha hy
    have : Real.exp 6 ≤ Real.exp (3 * ustar a y) := by rw [h3, le_div_iff₀ hpa]; linarith
    have := Real.exp_le_exp.1 this; linarith
  obtain ⟨hI1, hI2, hmid⟩ := hstep y hy hΛ hu

  have hSout : MeasurableSet {v : ℝ | δ' < |v|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hSwin : MeasurableSet {v : ℝ | |v| ≤ δ'} := measurableSet_le continuous_abs.measurable measurable_const
  have hSfl : MeasurableSet (Set.Iio (-2 : ℝ)) := measurableSet_Iio

  have hGt_eq_win : ∀ v ∈ {v : ℝ | |v| ≤ δ'}, Gt a α β y v = G a α β y v := by
    intro v hv; exact Gt_of_ge a α β y (by have : |v| ≤ δ' := hv; linarith [neg_abs_le v])
  have hIwin : IntegrableOn (G a α β y) {v : ℝ | |v| ≤ δ'} := hI2.congr_fun hGt_eq_win hSwin
  have hwin_eq : ∫ v in {v : ℝ | |v| ≤ δ'}, Gt a α β y v = ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v :=
    setIntegral_congr_fun hSwin hGt_eq_win

  have hmid' : ∫ v in {v : ℝ | δ' < |v|}, Gt a α β y v ≤ (ε / 2) * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v := by
    rw [← hwin_eq]
    refine hmid.trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg (fun v => Gt_nonneg a ha α β y v)))
    have := hL₁ (Lam a y) hΛ1
    rw [Real.sqrt_eq_rpow]
    rw [show -(Lam a y * min (OcLong.phi 0 - OcLong.phi δ') (OcLong.phi 0 - OcLong.phi (-δ')) / 2) = -(γ / 2) * Lam a y by rw [hγ]; ring]
    exact this

  obtain ⟨hfl_int, hfl_le⟩ := farleft_integral a ha α β hy hΛ (by rw [← hκ, ← hk]; exact hyk)
  have hwin_lb := window_lb a ha α β hy hΛ hu hρ0 hρδ hδ'1 hρin hIwin
  have hfl_eps : ∫ v in Set.Iio (-2), G a α β y v ≤ (ε / 2) * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v := by
    have hdec := hL₂ (Lam a y) hΛ2
    have hid := farleft_identity a ha α β hy k W γ hW0.ne'
    rw [← hκ] at hfl_le
    rw [← hD, ← hb] at hid
    calc ∫ v in Set.Iio (-2), G a α β y v ≤ _ := hfl_le
      _ = _ := hid
      _ ≤ (ε / 2) * (W * (Real.sqrt (Lam a y))⁻¹ * Real.exp (Lam a y * (OcLong.phi 0 - γ / 2))) :=
          mul_le_mul_of_nonneg_right hdec (by positivity)
      _ ≤ (ε / 2) * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v := by
          exact mul_le_mul_of_nonneg_left hwin_lb (by positivity)

  have hGsplit : ∀ v, G a α β y v = Gt a α β y v + Set.indicator (Set.Iio (-2)) (G a α β y) v := by
    intro v
    rcases le_or_gt (-2) v with h | h
    · rw [Gt_of_ge a α β y h, Set.indicator_of_notMem (by simp [h]), add_zero]
    · rw [Gt_of_lt a α β y h, Set.indicator_of_mem (by exact h), zero_add]
  have hGfar_int : Integrable (Set.indicator (Set.Iio (-2)) (G a α β y)) :=
    (integrable_indicator_iff hSfl).2 hfl_int
  have hGt_int : Integrable (Gt a α β y) := by
    have : {v : ℝ | δ' < |v|} ∪ {v : ℝ | |v| ≤ δ'} = Set.univ := by
      ext v
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases le_or_gt |v| δ' with h | h
      · exact Or.inr h
      · exact Or.inl h
    have h := hI1.union hI2
    rw [this, integrableOn_univ] at h; exact h
  have hG_int : Integrable (G a α β y) := by
    have := hGt_int.add hGfar_int
    exact this.congr (ae_of_all _ (fun v => (hGsplit v).symm))
  refine ⟨hG_int, ?_⟩

  have hG0 : ∀ v, 0 ≤ G a α β y v := fun v => G_nonneg a ha α β y v
  have hsub : {v : ℝ | δ₁ < |v|} ⊆ {v : ℝ | δ' < |v|} := fun v hv => lt_of_le_of_lt hδ'δ hv
  have step1 : ∫ v in {v : ℝ | δ₁ < |v|}, G a α β y v ≤ ∫ v in {v : ℝ | δ' < |v|}, G a α β y v :=
    setIntegral_mono_set hG_int.integrableOn (ae_of_all _ hG0) (ae_of_all _ hsub)
  have step2 : ∫ v in {v : ℝ | δ' < |v|}, G a α β y v
      = (∫ v in {v : ℝ | δ' < |v|}, Gt a α β y v) + (∫ v in {v : ℝ | δ' < |v|}, Set.indicator (Set.Iio (-2)) (G a α β y) v) := by
    rw [setIntegral_congr_fun hSout (fun v _ => hGsplit v)]
    exact integral_add hI1 hGfar_int.integrableOn
  have step3 : ∫ v in {v : ℝ | δ' < |v|}, Set.indicator (Set.Iio (-2)) (G a α β y) v ≤ ∫ v in Set.Iio (-2), G a α β y v := by
    calc ∫ v in {v : ℝ | δ' < |v|}, Set.indicator (Set.Iio (-2)) (G a α β y) v
        ≤ ∫ v, Set.indicator (Set.Iio (-2)) (G a α β y) v :=
          setIntegral_le_integral hGfar_int (ae_of_all _ (fun v => Set.indicator_nonneg (fun w _ => hG0 w) _))
      _ = ∫ v in Set.Iio (-2), G a α β y v := integral_indicator hSfl
  have step4 : ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v ≤ ∫ v, G a α β y v :=
    setIntegral_le_integral hG_int (ae_of_all _ hG0)
  calc ∫ v in {v : ℝ | δ₁ < |v|}, G a α β y v ≤ ∫ v in {v : ℝ | δ' < |v|}, G a α β y v := step1
    _ ≤ ((ε / 2) * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v) + ((ε / 2) * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v) := by
        rw [step2]; exact add_le_add hmid' (step3.trans hfl_eps)
    _ = ε * ∫ v in {v : ℝ | |v| ≤ δ'}, G a α β y v := by ring
    _ ≤ ε * ∫ v, G a α β y v := mul_le_mul_of_nonneg_left step4 hε.le

end LC

namespace LC

theorem long_conc_F (a : ℝ) (ha : a ≠ 0) (α β : ℝ) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      Integrable (fun u => Real.exp (E a α β y u) * Zfull a α β u) ∧
      ∫ u in {u : ℝ | δ₁ < |u - ustar a y|}, Real.exp (E a α β y u) * Zfull a α β u
        ≤ ε * ∫ u, Real.exp (E a α β y u) * Zfull a α β u := by
  obtain ⟨R, hR⟩ := long_conc_G a ha α β hδ₁ hε
  refine ⟨R, fun y hy => ?_⟩
  obtain ⟨hGint, hGle⟩ := hR y hy
  set K₀ : ℝ := (β + 1 + (α - β) / 2) * ustar a y - ((α - β) / 2) * Real.log |a| with hK₀
  set F : ℝ → ℝ := fun u => Real.exp (E a α β y u) * Zfull a α β u with hF
  have hshift : ∀ v, F (ustar a y + v) = Real.exp K₀ * G a α β y v := fun v => F_eq_const_mul_G a ha α β y v
  have hFint : Integrable F := by
    have h1 : Integrable (fun v => F (ustar a y + v)) := by
      simp_rw [hshift]; exact hGint.const_mul _
    have h2 := h1.comp_sub_right (ustar a y)
    refine h2.congr (ae_of_all _ (fun u => ?_))
    simp only []
    congr 1; ring
  refine ⟨hFint, ?_⟩
  rw [setIntegral_comp_ustar F (ustar a y) δ₁, integral_comp_ustar F (ustar a y)]
  simp_rw [hshift]
  rw [integral_const_mul, integral_const_mul, ← mul_assoc, mul_comm ε, mul_assoc]
  exact mul_le_mul_of_nonneg_left hGle (Real.exp_nonneg _)

end LC

end OcConc

theorem solution
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ₁ : ℝ) (hη : 0 < η) (hδ₁ : 0 < δ₁) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      Integrable (fun u : ℝ =>
        Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
            + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
          * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))) ∧
      ∫ u in {u : ℝ | δ₁ < |u - (1 / 3) * Real.log (y / (Real.pi * |a|))|},
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ))
        ≤ η * ∫ u : ℝ,
          Real.exp (-y * Real.log (1 + Real.exp (-2 * u)) + (β + 1) * u
              + (α - β) * ((1 / 4) * Real.log ((1 + Real.exp (2 * u)) / a ^ 2)))
            * ∫ σ : ℝ, Real.exp ((α - β) * σ - 2 * Real.pi * Real.sqrt (a ^ 2 * (1 + Real.exp (2 * u))) * Real.cosh (2 * σ)) :=
  OcConc.LC.long_conc_F a ha α β hδ₁ hη

end S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_integrable_and_setIntegral_longitudinal_compl_window_le_mul_integral (solution)
