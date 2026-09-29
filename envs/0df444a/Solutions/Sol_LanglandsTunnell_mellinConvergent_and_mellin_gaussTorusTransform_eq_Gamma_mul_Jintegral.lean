-- Prove2me | solution 1 for LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f1b45e67-842c-5231-9b3d-7d2a88f5f264

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral

set_option autoImplicit false

open MeasureTheory Set Real

namespace MGReal

noncomputable def F (a p q κ x : ℝ) (σ w r : ℝ) : ℝ :=
  σ ^ (x - 1) * rexp (-(π * a ^ 2 * σ ^ 2)) *
    ((|a| * σ / w) * (4 * (r ^ p * rexp (-(π * r ^ 2)) * ((|a| * σ / w / r) ^ q * rexp (-(π * (|a| * σ / w / r) ^ 2))) / r)) *
      w ^ κ * rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))))

noncomputable def Φ (a p q κ : ℝ) (w r : ℝ) : ℝ :=
  w ^ (κ - 1 - q) * r ^ (p - q - 1) * rexp (-(π * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))

noncomputable def ψ (w r : ℝ) : ℝ := (1 + ((w * r) ^ 2)⁻¹)⁻¹

theorem ψ_pos {w r : ℝ} (hw : 0 < w) (hr : 0 < r) : 0 < ψ w r := by
  unfold ψ; positivity

theorem ψ_lt_one {w r : ℝ} (hw : 0 < w) (hr : 0 < r) : ψ w r < 1 := by
  unfold ψ
  have : 0 < ((w * r) ^ 2)⁻¹ := by positivity
  rw [inv_lt_one_iff₀]; right; linarith

theorem Φ_pos (a p q κ : ℝ) {w r : ℝ} (hw : 0 < w) (hr : 0 < r) : 0 < Φ a p q κ w r := by
  unfold Φ; positivity

theorem F_eq (a p q κ x : ℝ) (ha : a ≠ 0) {σ w r : ℝ} (hσ : 0 < σ) (hw : 0 < w) (hr : 0 < r) :
    F a p q κ x σ w r =
      (σ ^ (x + q) * rexp (-(π * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹)) * σ ^ 2)) * (4 * |a| ^ (1 + q) * Φ a p q κ w r) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  unfold F Φ

  rw [Real.div_rpow (by positivity) hr.le, Real.div_rpow (by positivity) hw.le, Real.mul_rpow ha'.le hσ.le]

  have hexp : rexp (-(π * a ^ 2 * σ ^ 2)) * rexp (-(π * r ^ 2)) * rexp (-(π * (|a| * σ / w / r) ^ 2)) *
      rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) =
      rexp (-(π * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹)) * σ ^ 2) * rexp (-(π * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have : (|a| * σ / w / r) ^ 2 = a ^ 2 * σ ^ 2 * ((w * r) ^ 2)⁻¹ := by
      rw [div_div, div_pow, mul_pow, sq_abs]; ring
    rw [this]; ring

  have hσp : σ ^ (x - 1) * σ * σ ^ q = σ ^ (x + q) := by
    rw [show x + q = (x - 1) + 1 + q by ring, Real.rpow_add hσ, Real.rpow_add hσ, Real.rpow_one]
  have hwp : w ^ κ * (w⁻¹ * (w ^ q)⁻¹) = w ^ (κ - 1 - q) := by
    rw [show κ - 1 - q = κ + (-1) + (-q) by ring, Real.rpow_add hw, Real.rpow_add hw, Real.rpow_neg_one,
      Real.rpow_neg hw.le]; ring
  have hrp : r ^ p * (r ^ q)⁻¹ * r⁻¹ = r ^ (p - q - 1) := by
    rw [show p - q - 1 = p + (-q) + (-1) by ring, Real.rpow_add hr, Real.rpow_add hr, Real.rpow_neg_one,
      Real.rpow_neg hr.le]

  have hw0 : w ≠ 0 := hw.ne'
  have hr0 : r ≠ 0 := hr.ne'
  calc σ ^ (x - 1) * rexp (-(π * a ^ 2 * σ ^ 2)) *
        (|a| * σ / w * (4 * (r ^ p * rexp (-(π * r ^ 2)) *
          (|a| ^ q * σ ^ q / w ^ q / r ^ q * rexp (-(π * (|a| * σ / w / r) ^ 2))) / r)) *
          w ^ κ * rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))))
      = 4 * (|a| * |a| ^ q) * (σ ^ (x - 1) * σ * σ ^ q) * (w ^ κ * (w⁻¹ * (w ^ q)⁻¹)) * (r ^ p * (r ^ q)⁻¹ * r⁻¹) *
          (rexp (-(π * a ^ 2 * σ ^ 2)) * rexp (-(π * r ^ 2)) * rexp (-(π * (|a| * σ / w / r) ^ 2)) *
            rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) := by
        field_simp
    _ = _ := by
        rw [hσp, hwp, hrp, hexp, Real.rpow_add ha' 1 q, Real.rpow_one]
        ring

theorem integral_sigma (A B : ℝ) (hA : -1 < A) (hB : 0 < B) :
    ∫ σ in Ioi (0:ℝ), σ ^ A * rexp (-B * σ ^ 2) = B ^ (-(A + 1) / 2) * (1 / 2) * Real.Gamma ((A + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := A) (b := B) two_pos hA hB
  simp_rw [Real.rpow_two] at h
  exact h

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem measurable_Φ (a p q κ : ℝ) : Measurable (Function.uncurry (Φ a p q κ)) := by
  unfold Φ
  have h1 : Measurable fun z : ℝ × ℝ => z.1 ^ (κ - 1 - q) := measurable_fst.pow_const _
  have h2 : Measurable fun z : ℝ × ℝ => z.2 ^ (p - q - 1) := measurable_snd.pow_const _
  have h3 : Measurable fun z : ℝ × ℝ => rexp (-(π * (z.2 ^ 2 + (z.1 ^ 2)⁻¹ + a ^ 2 * z.1 ^ 2))) := by fun_prop
  exact (h1.mul h2).mul h3

theorem measurable_ψ : Measurable (Function.uncurry ψ) := by
  unfold ψ
  exact ((measurable_const.add ((measurable_fst.mul measurable_snd).pow_const 2).inv).inv)

theorem measurable_ψpowΦ (a p q κ Z : ℝ) :
    Measurable (fun z : ℝ × ℝ => ψ z.1 z.2 ^ Z * Φ a p q κ z.1 z.2) :=
  (measurable_ψ.pow_const Z).mul (measurable_Φ a p q κ)

theorem ψ_rpow_le {w r : ℝ} (hw : 0 < w) (hr : 0 < r) {Z θ : ℝ} (hθ : 0 ≤ θ) (hθZ : θ ≤ Z) :
    ψ w r ^ Z ≤ (w * r) ^ (2 * θ) := by
  have hψ := ψ_pos hw hr
  have hψ1 := (ψ_lt_one hw hr).le
  have hwr : 0 < w * r := mul_pos hw hr

  have h1 : ψ w r ^ Z ≤ ψ w r ^ θ := Real.rpow_le_rpow_of_exponent_ge hψ hψ1 hθZ
  have h2 : ψ w r ≤ (w * r) ^ 2 := by
    unfold ψ
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : 0 < (w * r) ^ 2 := by positivity
    field_simp
    nlinarith
  calc ψ w r ^ Z ≤ ψ w r ^ θ := h1
    _ ≤ ((w * r) ^ 2) ^ θ := Real.rpow_le_rpow hψ.le h2 hθ
    _ = (w * r) ^ (2 * θ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hwr.le]; norm_num

theorem integrableOn_w (a : ℝ) (ha : a ≠ 0) (s : ℝ) :
    IntegrableOn (fun w : ℝ => w ^ s * rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) (Ioi 0) := by

  obtain ⟨n, hn⟩ : ∃ n : ℕ, -1 < s + 2 * n := ⟨Nat.ceil (|s| + 1), by
    have := Nat.le_ceil (|s| + 1); have := abs_nonneg s; have := neg_abs_le s; push_cast; linarith⟩
  have hb : 0 < π * a ^ 2 := by positivity
  have hdom := (integrableOn_rpow_mul_exp_neg_mul_sq hb hn).const_mul ((n.factorial : ℝ) * π⁻¹ ^ n)
  refine Integrable.mono' hdom ?_ ?_
  · refine ((measurable_id.pow_const s).mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hx : 0 < π * (w ^ 2)⁻¹ := by positivity

    have hexp : rexp (-(π * (w ^ 2)⁻¹)) ≤ n.factorial * (π⁻¹ ^ n * w ^ (2 * (n : ℝ))) := by
      have h := Real.add_one_le_exp (π * (w ^ 2)⁻¹)
      have key : (π * (w ^ 2)⁻¹) ^ n / n.factorial ≤ rexp (π * (w ^ 2)⁻¹) := by
        have := Real.pow_div_factorial_le_exp (π * (w ^ 2)⁻¹) hx.le n
        exact this
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      · have hfac : (0 : ℝ) < n.factorial := by positivity
        rw [div_le_iff₀ hfac] at key
        have hw2n : w ^ (2 * (n : ℝ)) = (w ^ 2) ^ n := by
          rw [← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
        calc (1 : ℝ) = (π * (w ^ 2)⁻¹) ^ n * (π⁻¹ ^ n * w ^ (2 * (n : ℝ))) := by
              rw [hw2n, mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
              have : π * (w ^ 2)⁻¹ * (π⁻¹ * w ^ 2) = 1 := by field_simp
              rw [this, one_pow]
          _ ≤ rexp (π * (w ^ 2)⁻¹) * n.factorial * (π⁻¹ ^ n * w ^ (2 * (n : ℝ))) := by
              gcongr
          _ = n.factorial * (π⁻¹ ^ n * w ^ (2 * (n : ℝ))) * rexp (π * (w ^ 2)⁻¹) := by ring
    have hsplit : rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) = rexp (-(π * (w ^ 2)⁻¹)) * rexp (-(π * a ^ 2) * w ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    have hws : 0 ≤ w ^ s := Real.rpow_nonneg hw.le s
    have he2 : 0 ≤ rexp (-(π * a ^ 2) * w ^ 2) := (Real.exp_pos _).le
    calc w ^ s * (rexp (-(π * (w ^ 2)⁻¹)) * rexp (-(π * a ^ 2) * w ^ 2))
        ≤ w ^ s * (n.factorial * (π⁻¹ ^ n * w ^ (2 * (n : ℝ))) * rexp (-(π * a ^ 2) * w ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp he2) hws
      _ = (n.factorial : ℝ) * π⁻¹ ^ n * (w ^ (s + 2 * n) * rexp (-(π * a ^ 2) * w ^ 2)) := by
          rw [Real.rpow_add hw]; push_cast; ring

noncomputable def J (a p q κ Z : ℝ) : ℝ :=
  ∫ v, ψ v.1 v.2 ^ Z * Φ a p q κ v.1 v.2 ∂((μ0).prod (μ0))

theorem ae_pos_prod : ∀ᵐ v : ℝ × ℝ ∂((μ0).prod (μ0)), 0 < v.1 ∧ 0 < v.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with v hv
  exact ⟨hv.1, hv.2⟩

theorem ψ_le_sq {w r : ℝ} (hw : 0 < w) (hr : 0 < r) : ψ w r ≤ (w * r) ^ 2 := by
  unfold ψ
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have : 0 < (w * r) ^ 2 := by positivity
  field_simp
  nlinarith

theorem integrable_ψΦ (a p q κ Z : ℝ) (ha : a ≠ 0) (hZ : 0 ≤ Z) (hpqZ : -1 < p - q - 1 + 2 * Z) :
    Integrable (fun v : ℝ × ℝ => ψ v.1 v.2 ^ Z * Φ a p q κ v.1 v.2) ((μ0).prod (μ0)) := by
  have hw := integrableOn_w a ha (κ - 1 - q + 2 * Z)
  have hr : IntegrableOn (fun r : ℝ => r ^ (p - q - 1 + 2 * Z) * rexp (-π * r ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos hpqZ
  have hdom := hw.mul_prod hr
  refine Integrable.mono' hdom (measurable_ψpowΦ a p q κ Z).aestronglyMeasurable ?_
  filter_upwards [ae_pos_prod] with v hv
  obtain ⟨w, r⟩ := v
  obtain ⟨hw0, hr0⟩ := hv
  simp only at hw0 hr0 ⊢
  have hψ0 := (ψ_pos hw0 hr0).le
  have hΦ0 := (Φ_pos a p q κ hw0 hr0).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hψ0 Z) hΦ0)]
  have hψb : ψ w r ^ Z ≤ w ^ (2 * Z) * r ^ (2 * Z) := by
    calc ψ w r ^ Z ≤ ((w * r) ^ 2) ^ Z := Real.rpow_le_rpow hψ0 (ψ_le_sq hw0 hr0) hZ
      _ = w ^ (2 * Z) * r ^ (2 * Z) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_pos hw0 hr0).le, Real.mul_rpow hw0.le hr0.le]; norm_num
  calc ψ w r ^ Z * Φ a p q κ w r ≤ (w ^ (2 * Z) * r ^ (2 * Z)) * Φ a p q κ w r :=
        mul_le_mul_of_nonneg_right hψb hΦ0
    _ = w ^ (κ - 1 - q + 2 * Z) * rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) *
          (r ^ (p - q - 1 + 2 * Z) * rexp (-π * r ^ 2)) := by
        unfold Φ
        rw [Real.rpow_add hw0, Real.rpow_add hr0,
          show rexp (-(π * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) =
            rexp (-(π * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) * rexp (-π * r ^ 2) by rw [← Real.exp_add]; congr 1; ring]
        ring

theorem J_pos (a p q κ Z : ℝ) (ha : a ≠ 0) (hZ : 0 ≤ Z) (hpqZ : -1 < p - q - 1 + 2 * Z) : 0 < J a p q κ Z := by
  unfold J
  refine integral_pos_iff_support_of_nonneg_ae ?_ (integrable_ψΦ a p q κ Z ha hZ hpqZ) |>.2 ?_
  · filter_upwards [ae_pos_prod] with v hv
    exact mul_nonneg (Real.rpow_nonneg (ψ_pos hv.1 hv.2).le Z) (Φ_pos a p q κ hv.1 hv.2).le
  ·
    have hsub : Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) ⊆ Function.support (fun v : ℝ × ℝ => ψ v.1 v.2 ^ Z * Φ a p q κ v.1 v.2) := by
      intro v hv
      rw [Function.mem_support]
      exact (mul_pos (Real.rpow_pos_of_pos (ψ_pos hv.1 hv.2) Z) (Φ_pos a p q κ hv.1 hv.2)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.prod_restrict, Measure.restrict_apply' (measurableSet_Ioi.prod measurableSet_Ioi), Set.inter_self,
      Measure.prod_prod]
    simp [Real.volume_Ioi]

noncomputable def Kc (a q Z : ℝ) : ℝ := 2 * |a| ^ (1 + q) * Real.Gamma Z * (π * a ^ 2) ^ (-Z)

theorem Kc_pos (a q Z : ℝ) (ha : a ≠ 0) (hZ : 0 < Z) : 0 < Kc a q Z := by
  unfold Kc
  have := Real.Gamma_pos_of_pos hZ
  have : 0 < |a| := abs_pos.2 ha
  positivity

theorem sigma_section (a p q κ x : ℝ) (ha : a ≠ 0) (hxq : -1 < x + q) {w r : ℝ} (hw : 0 < w) (hr : 0 < r) :
    IntegrableOn (fun σ => F a p q κ x σ w r) (Ioi 0) ∧
    ∫ σ in Ioi (0:ℝ), F a p q κ x σ w r =
      Kc a q ((x + q + 1) / 2) * (ψ w r ^ ((x + q + 1) / 2) * Φ a p q κ w r) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  set B : ℝ := π * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  set c : ℝ := 4 * |a| ^ (1 + q) * Φ a p q κ w r with hc
  have hpt : ∀ σ : ℝ, σ ∈ Ioi (0:ℝ) → F a p q κ x σ w r = (σ ^ (x + q) * rexp (-B * σ ^ 2)) * c := by
    intro σ hσ
    rw [F_eq a p q κ x ha hσ hw hr, hB, hc, neg_mul]
  have hI : IntegrableOn (fun σ : ℝ => (σ ^ (x + q) * rexp (-B * σ ^ 2)) * c) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hB0 hxq).mul_const c
  refine ⟨hI.congr_fun (fun σ hσ => (hpt σ hσ).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_mul_const, integral_sigma _ _ hxq hB0]

  have hZ : -(x + q + 1) / 2 = -((x + q + 1) / 2) := by ring
  have hψ : ψ w r = (1 + ((w * r) ^ 2)⁻¹)⁻¹ := rfl
  rw [hZ, hB, Real.mul_rpow (by positivity) (by positivity), hc, Kc, hψ, Real.inv_rpow (by positivity),
    Real.rpow_neg (le_of_lt (by positivity : (0:ℝ) < 1 + ((w * r) ^ 2)⁻¹))]
  ring

theorem measurable_F (a p q κ x : ℝ) : Measurable (fun z : ℝ × ℝ × ℝ => F a p q κ x z.1 z.2.1 z.2.2) := by
  have m1 : Measurable fun z : ℝ × ℝ × ℝ => z.1 := measurable_fst
  have m2 : Measurable fun z : ℝ × ℝ × ℝ => z.2.1 := measurable_fst.comp measurable_snd
  have m3 : Measurable fun z : ℝ × ℝ × ℝ => z.2.2 := measurable_snd.comp measurable_snd
  have t : Measurable fun z : ℝ × ℝ × ℝ => |a| * z.1 / z.2.1 := (m1.const_mul _).div m2
  have e1 : Measurable fun z : ℝ × ℝ × ℝ => rexp (-(π * a ^ 2 * z.1 ^ 2)) := by fun_prop
  have e2 : Measurable fun z : ℝ × ℝ × ℝ => rexp (-(π * z.2.2 ^ 2)) := by fun_prop
  have e3 : Measurable fun z : ℝ × ℝ × ℝ => rexp (-(π * (|a| * z.1 / z.2.1 / z.2.2) ^ 2)) :=
    Real.measurable_exp.comp (((t.div m3).pow_const 2).const_mul π).neg
  have e4 : Measurable fun z : ℝ × ℝ × ℝ => rexp (-(π * ((z.2.1 ^ 2)⁻¹ + a ^ 2 * z.2.1 ^ 2))) := by fun_prop
  have h : Measurable fun z : ℝ × ℝ × ℝ =>
      z.1 ^ (x - 1) * rexp (-(π * a ^ 2 * z.1 ^ 2)) *
        ((|a| * z.1 / z.2.1) * (4 * (z.2.2 ^ p * rexp (-(π * z.2.2 ^ 2)) *
          ((|a| * z.1 / z.2.1 / z.2.2) ^ q * rexp (-(π * (|a| * z.1 / z.2.1 / z.2.2) ^ 2))) / z.2.2)) *
          z.2.1 ^ κ * rexp (-(π * ((z.2.1 ^ 2)⁻¹ + a ^ 2 * z.2.1 ^ 2)))) :=
    ((m1.pow_const _).mul e1).mul (((t.mul ((((m3.pow_const _).mul e2).mul (((t.div m3).pow_const _).mul e3)).div m3
      |>.const_mul _)).mul (m2.pow_const _)).mul e4)
  exact h

theorem ae_pos_triple : ∀ᵐ z : ℝ × ℝ × ℝ ∂((μ0).prod ((μ0).prod (μ0))), 0 < z.1 ∧ (0 < z.2.1 ∧ 0 < z.2.2) := by
  have h1 : ∀ᵐ s : ℝ ∂(μ0), 0 < s := ae_restrict_mem measurableSet_Ioi
  exact ((Measure.quasiMeasurePreserving_fst).ae h1).and ((Measure.quasiMeasurePreserving_snd).ae ae_pos_prod)

theorem lintegral_F (a p q κ x : ℝ) (ha : a ≠ 0) (hxq : -1 < x + q) (hxp : -1 < x + p) :
    ∫⁻ z, ENNReal.ofReal (F a p q κ x z.1 z.2.1 z.2.2) ∂((μ0).prod ((μ0).prod (μ0))) =
      ENNReal.ofReal (Kc a q ((x + q + 1) / 2) * J a p q κ ((x + q + 1) / 2)) := by
  set Z : ℝ := (x + q + 1) / 2 with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; linarith
  have hpqZ : -1 < p - q - 1 + 2 * Z := by rw [hZ]; linarith
  have hmeas : AEMeasurable (fun z : ℝ × ℝ × ℝ => ENNReal.ofReal (F a p q κ x z.1 z.2.1 z.2.2))
      ((μ0).prod ((μ0).prod (μ0))) := (measurable_F a p q κ x).ennreal_ofReal.aemeasurable
  rw [lintegral_prod_symm _ hmeas]
  have hinner : ∀ᵐ v : ℝ × ℝ ∂((μ0).prod (μ0)),
      ∫⁻ σ, ENNReal.ofReal (F a p q κ x σ v.1 v.2) ∂(μ0) = ENNReal.ofReal (Kc a q Z * (ψ v.1 v.2 ^ Z * Φ a p q κ v.1 v.2)) := by
    filter_upwards [ae_pos_prod] with v hv
    obtain ⟨hI, hval⟩ := sigma_section a p q κ x ha hxq hv.1 hv.2
    rw [← ofReal_integral_eq_lintegral_ofReal hI, hval]
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun σ (hσ : 0 < σ) => ?_)
    show (0 : ℝ) ≤ F a p q κ x σ v.1 v.2
    rw [F_eq a p q κ x ha hσ hv.1 hv.2]
    have hΦ := Φ_pos a p q κ hv.1 hv.2
    have : 0 < |a| := abs_pos.2 ha
    positivity
  rw [lintegral_congr_ae hinner]
  have hI2 := (integrable_ψΦ a p q κ Z ha hZ0 hpqZ).const_mul (Kc a q Z)
  rw [← ofReal_integral_eq_lintegral_ofReal hI2, integral_const_mul]
  · rfl
  · filter_upwards [ae_pos_prod] with v hv
    have hK : 0 < Kc a q Z := Kc_pos a q Z ha (by rw [hZ]; linarith)
    exact mul_nonneg hK.le (mul_nonneg (Real.rpow_nonneg (ψ_pos hv.1 hv.2).le Z) (Φ_pos a p q κ hv.1 hv.2).le)

theorem integrable_F (a p q κ x : ℝ) (ha : a ≠ 0) (hxq : -1 < x + q) (hxp : -1 < x + p) :
    Integrable (fun z : ℝ × ℝ × ℝ => F a p q κ x z.1 z.2.1 z.2.2) ((μ0).prod ((μ0).prod (μ0))) := by
  have hnn : 0 ≤ᵐ[(μ0).prod ((μ0).prod (μ0))] fun z : ℝ × ℝ × ℝ => F a p q κ x z.1 z.2.1 z.2.2 := by
    filter_upwards [ae_pos_triple] with z hz
    obtain ⟨h1, h2, h3⟩ := hz
    show (0 : ℝ) ≤ F a p q κ x z.1 z.2.1 z.2.2
    rw [F_eq a p q κ x ha h1 h2 h3]
    have hΦ := Φ_pos a p q κ h2 h3
    have : 0 < |a| := abs_pos.2 ha
    positivity
  refine ⟨(measurable_F a p q κ x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn, lintegral_F a p q κ x ha hxq hxp]
  exact ENNReal.ofReal_lt_top

theorem closed_form (a p q κ x : ℝ) (ha : a ≠ 0) (hxq : -1 < x + q) (hxp : -1 < x + p) :
    ∫ σ in Ioi (0:ℝ), ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), F a p q κ x σ w r =
      Kc a q ((x + q + 1) / 2) * J a p q κ ((x + q + 1) / 2) := by
  set Z : ℝ := (x + q + 1) / 2 with hZ
  have hF := integrable_F a p q κ x ha hxq hxp

  have h1 : ∀ᵐ σ : ℝ ∂(μ0), ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), F a p q κ x σ w r =
      ∫ v, F a p q κ x σ v.1 v.2 ∂((μ0).prod (μ0)) := by
    filter_upwards [hF.prod_right_ae] with σ hσ
    exact (integral_prod (fun v : ℝ × ℝ => F a p q κ x σ v.1 v.2) hσ).symm
  rw [integral_congr_ae h1, ← integral_prod _ hF, integral_prod_symm _ hF]

  have h2 : ∀ᵐ v : ℝ × ℝ ∂((μ0).prod (μ0)), ∫ σ, F a p q κ x σ v.1 v.2 ∂(μ0) = Kc a q Z * (ψ v.1 v.2 ^ Z * Φ a p q κ v.1 v.2) := by
    filter_upwards [ae_pos_prod] with v hv
    exact (sigma_section a p q κ x ha hxq hv.1 hv.2).2
  rw [integral_congr_ae h2, integral_const_mul]
  rfl

end MGReal

namespace JForm

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

noncomputable def Hc (a : ℝ) (C p q κ : ℂ) : ℝ → ℂ :=
  fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

noncomputable def Rc (a : ℝ) (p q : ℂ) (σ' w r : ℝ) : ℂ :=
  ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
    ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ)

noncomputable def Fc (a : ℝ) (C p q κ z : ℂ) (σ' w r : ℝ) : ℂ :=
  ((σ' : ℝ) : ℂ) ^ (z - 1) * ((Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
    ((C * (((|a| * σ' / w : ℝ)) : ℂ) * ((4 : ℂ) * Rc a p q σ' w r)) *
      ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)))

noncomputable def Jc' (a : ℝ) (p q κ z : ℂ) (w r : ℝ) : ℂ :=
  (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
    (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

noncomputable def Jc (a : ℝ) (p q κ z : ℂ) (v : ℝ × ℝ) : ℂ :=
  (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
    (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ)

theorem Jc_eq (a : ℝ) (p q κ z : ℂ) (v : ℝ × ℝ) : Jc a p q κ z v = Jc' a p q κ z v.1 v.2 := rfl

theorem Jc'_eq (a : ℝ) (p q κ z : ℂ) (w r : ℝ) : Jc' a p q κ z w r = Jc a p q κ z (w, r) := rfl

noncomputable def Φc (a : ℝ) (p q κ : ℂ) (w r : ℝ) : ℂ :=
  ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) * (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

theorem Jc'_eq_mul_Φc (a : ℝ) (p q κ z : ℂ) (w r : ℝ) :
    Jc' a p q κ z w r = (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * Φc a p q κ w r := by
  unfold Jc' Φc; ring

example (a : ℝ) (C p q κ : ℂ) (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)) :
    H = Hc a C p q κ := hH

theorem mellin_integrand_eq_iter (a : ℝ) (C p q κ z : ℂ) (σ' : ℝ) :
    ((σ' : ℝ) : ℂ) ^ (z - 1) • Hc a C p q κ σ' = ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), Fc a C p q κ z σ' w r := by
  simp only [Hc, Fc, Rc, smul_eq_mul]
  simp only [← integral_const_mul, ← integral_mul_const]

end JForm

namespace JForm

open MGReal

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

theorem norm_ofReal_exp (x : ℝ) : ‖((rexp x : ℝ) : ℂ)‖ = rexp x := norm_ofReal_of_nonneg (Real.exp_pos x).le

theorem norm_Rc (a : ℝ) (ha : a ≠ 0) (p q : ℂ) {σ' w r : ℝ} (hσ : 0 < σ') (hw : 0 < w) (hr : 0 < r) :
    ‖Rc a p q σ' w r‖ =
      r ^ p.re * rexp (-(π * r ^ 2)) * ((|a| * σ' / w / r) ^ q.re * rexp (-(π * (|a| * σ' / w / r) ^ 2))) / r := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hτr : 0 < |a| * σ' / w / r := by positivity
  unfold Rc
  simp only [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hτr,
    norm_ofReal_exp, norm_ofReal_of_nonneg hr.le]

theorem norm_Fc (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) {σ' w r : ℝ} (hσ : 0 < σ') (hw : 0 < w) (hr : 0 < r) :
    ‖Fc a C p q κ z σ' w r‖ = ‖C‖ * F a p.re q.re κ.re z.re σ' w r := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  have hτ : 0 ≤ |a| * σ' / w := by positivity
  unfold Fc F
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hσ, Complex.norm_cpow_eq_rpow_re_of_pos hw,
    norm_ofReal_exp, norm_ofReal_of_nonneg hτ, h4, norm_Rc a ha p q hσ hw hr, Complex.sub_re, Complex.one_re]
  ring

theorem norm_Jc (a : ℝ) (p q κ z : ℂ) {w r : ℝ} (hw : 0 < w) (hr : 0 < r) :
    ‖Jc a p q κ z (w, r)‖ = ψ w r ^ ((z + q + 1) / 2).re * Φ a p.re q.re κ.re w r := by
  have hb : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
  unfold Jc Φ ψ
  simp only []
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos hw,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, norm_ofReal_of_nonneg (Real.exp_pos _).le, Complex.neg_re, Complex.sub_re,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, Complex.one_re, Real.rpow_neg hb.le, ← Real.inv_rpow hb.le]
  ring

theorem measurable_Rc (a : ℝ) (p q : ℂ) :
    Measurable (fun t : ℝ × ℝ × ℝ => Rc a p q t.1 t.2.1 t.2.2) := by
  unfold Rc; fun_prop

theorem measurable_Fc (a : ℝ) (C p q κ z : ℂ) :
    Measurable (fun t : ℝ × ℝ × ℝ => Fc a C p q κ z t.1 t.2.1 t.2.2) := by
  unfold Fc Rc; fun_prop

theorem measurable_Jc (a : ℝ) (p q κ z : ℂ) : Measurable (Jc a p q κ z) := by
  unfold Jc; fun_prop

theorem integrable_Fc (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    Integrable (fun t : ℝ × (ℝ × ℝ) => Fc a C p q κ z t.1 t.2.1 t.2.2) ((μ0).prod ((μ0).prod (μ0))) := by
  have hxq : -1 < z.re + q.re := by simpa [Complex.add_re] using hzq
  have hxp : -1 < z.re + p.re := by simpa [Complex.add_re] using hzp
  have hF := (integrable_F a p.re q.re κ.re z.re ha hxq hxp).const_mul ‖C‖
  refine Integrable.mono' hF (measurable_Fc a C p q κ z).aestronglyMeasurable ?_
  filter_upwards [ae_pos_triple] with t ht
  exact (norm_Fc a ha C p q κ z ht.1 ht.2.1 ht.2.2).le

theorem integrable_Jc (a : ℝ) (ha : a ≠ 0) (p q κ z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    Integrable (Jc a p q κ z) ((μ0).prod (μ0)) := by
  have hxq : -1 < z.re + q.re := by simpa [Complex.add_re] using hzq
  have hxp : -1 < z.re + p.re := by simpa [Complex.add_re] using hzp
  have hZ : 0 ≤ ((z + q + 1) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    norm_num
    nlinarith
  have hZ' : ((z + q + 1) / 2).re = (z.re + q.re + 1) / 2 := by
    simp [Complex.add_re]
  have hpqZ : -1 < p.re - q.re - 1 + 2 * ((z + q + 1) / 2).re := by rw [hZ']; linarith
  have hI := integrable_ψΦ a p.re q.re κ.re (((z + q + 1) / 2).re) ha hZ hpqZ
  refine Integrable.mono' hI (measurable_Jc a p q κ z).aestronglyMeasurable ?_
  filter_upwards [ae_pos_prod] with v hv
  obtain ⟨w, r⟩ := v
  exact (norm_Jc a p q κ z hv.1 hv.2).le

theorem mellinConvergent_Hc (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent (Hc a C p q κ) z := by
  have hF := integrable_Fc a ha C p q κ z hzq hzp
  have hG1 : Integrable (fun σ' : ℝ => ∫ v, Fc a C p q κ z σ' v.1 v.2 ∂((μ0).prod (μ0))) (μ0) := hF.integral_prod_left
  have hG2 : ∀ᵐ σ' : ℝ ∂(μ0), (∫ v, Fc a C p q κ z σ' v.1 v.2 ∂((μ0).prod (μ0))) =
      ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), Fc a C p q κ z σ' w r := by
    filter_upwards [hF.prod_right_ae] with σ' hσ
    exact integral_prod (fun v : ℝ × ℝ => Fc a C p q κ z σ' v.1 v.2) hσ
  have hG : Integrable (fun σ' : ℝ => ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), Fc a C p q κ z σ' w r) (μ0) := hG1.congr hG2
  unfold MellinConvergent IntegrableOn
  exact hG.congr (ae_of_all _ fun σ' => (mellin_integrand_eq_iter a C p q κ z σ').symm)

end JForm

namespace JForm

theorem integral_cpow_mul_exp_neg_mul_sq (B : ℝ) (hB : 0 < B) (s : ℂ) (hs : -1 < s.re) :
    ∫ σ in Ioi (0:ℝ), (σ : ℂ) ^ s * (Real.exp (-(B * σ ^ 2)) : ℂ) =
      (1 / 2 : ℂ) * ((B : ℝ) : ℂ) ^ (-((s + 1) / 2)) * Complex.Gamma ((s + 1) / 2) := by
  set g : ℝ → ℂ := fun y => (1 / 2 : ℂ) * ((y : ℂ) ^ ((s + 1) / 2 - 1) * Complex.exp (-(B * y))) with hg
  have hsub := integral_comp_rpow_Ioi g (p := 2) two_ne_zero
  have hL : ∫ σ in Ioi (0:ℝ), (σ : ℂ) ^ s * (Real.exp (-(B * σ ^ 2)) : ℂ) =
      ∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have h21 : (2:ℝ) - 1 = 1 := by norm_num
    rw [h21, Real.rpow_one, abs_of_pos two_pos, hg]
    simp only
    rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hpow : ((x ^ (2:ℝ) : ℝ) : ℂ) ^ ((s + 1) / 2 - 1) = (x : ℂ) ^ (s - 1) := by
      rw [← Complex.cpow_mul_ofReal_nonneg hx.le]
      congr 1; push_cast; ring
    have hexp : Complex.exp (-(↑B * ↑(x ^ (2:ℝ)))) = (Real.exp (-(B * x ^ 2)) : ℂ) := by
      rw [Real.rpow_two]; push_cast; rfl
    rw [hpow, hexp]
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
    have hxs : (x : ℂ) * (x : ℂ) ^ (s - 1) = (x : ℂ) ^ s := by
      conv_rhs => rw [show s = 1 + (s - 1) by ring]
      rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    calc (x : ℂ) ^ s * (Real.exp (-(B * x ^ 2)) : ℂ)
        = ((x : ℂ) * (x : ℂ) ^ (s - 1)) * (Real.exp (-(B * x ^ 2)) : ℂ) := by rw [hxs]
      _ = 2 * (x : ℂ) * (1 / 2 * ((x : ℂ) ^ (s - 1) * (Real.exp (-(B * x ^ 2)) : ℂ))) := by ring
  rw [hL, hsub, hg]
  simp only
  rw [integral_const_mul]
  have ha : 0 < ((s + 1) / 2).re := by
    rw [Complex.div_re]; simp; linarith
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hB]
  have hBarg : ((B : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hB.le]; exact Real.pi_ne_zero.symm
  rw [one_div ((B:ℝ):ℂ), Complex.inv_cpow _ _ hBarg, ← Complex.cpow_neg]
  ring

theorem cpow_ofReal_mul' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (c : ℂ) :
    ((x * y : ℝ) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ c := by
  rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hx hy c

theorem cpow_ofReal_inv' {x : ℝ} (hx : 0 < x) (c : ℂ) : ((x⁻¹ : ℝ) : ℂ) ^ c = ((x : ℂ) ^ c)⁻¹ := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)]

theorem cpow_ofReal_div' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (c : ℂ) :
    ((x / y : ℝ) : ℂ) ^ c = (x : ℂ) ^ c * ((y : ℂ) ^ c)⁻¹ := by
  rw [div_eq_mul_inv, cpow_ofReal_mul' hx (inv_nonneg.2 hy.le), cpow_ofReal_inv' hy]

theorem Fc_eq (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) {σ w r : ℝ} (hσ : 0 < σ) (hw : 0 < w) (hr : 0 < r) :
    Fc a C p q κ z σ w r =
      ((σ : ℂ) ^ (z + q) * (Real.exp (-(Real.pi * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹) * σ ^ 2)) : ℂ)) *
        ((4 : ℂ) * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * Φc a p q κ w r) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hσ.ne'
  have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hA0 : ((|a| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha'.ne'

  have h1 : (σ : ℂ) ^ (z + q) = (σ : ℂ) ^ (z - 1) * (σ : ℂ) * (σ : ℂ) ^ q := by
    rw [show z + q = (z - 1) + 1 + q by ring, Complex.cpow_add _ _ hσ0, Complex.cpow_add _ _ hσ0,
      Complex.cpow_one]
  have h2 : (w : ℂ) ^ (κ - 1 - q) = (w : ℂ) ^ κ * (w : ℂ)⁻¹ * ((w : ℂ) ^ q)⁻¹ := by
    rw [Complex.cpow_sub _ _ hw0, Complex.cpow_sub _ _ hw0, Complex.cpow_one]; ring
  have h3 : (r : ℂ) ^ (p - q - 1) = (r : ℂ) ^ p * ((r : ℂ) ^ q)⁻¹ * (r : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hr0, Complex.cpow_sub _ _ hr0, Complex.cpow_one]; ring
  have h4 : ((|a| : ℝ) : ℂ) ^ (1 + q) = ((|a| : ℝ) : ℂ) * ((|a| : ℝ) : ℂ) ^ q := by
    rw [Complex.cpow_add _ _ hA0, Complex.cpow_one]
  have h5 : ((((|a| * σ / w) / r : ℝ)) : ℂ) ^ q =
      ((|a| : ℝ) : ℂ) ^ q * (σ : ℂ) ^ q * ((w : ℂ) ^ q)⁻¹ * ((r : ℂ) ^ q)⁻¹ := by
    rw [cpow_ofReal_div' (by positivity) hr, cpow_ofReal_div' (by positivity) hw,
      cpow_ofReal_mul' ha'.le hσ.le]
  have h6 : ((((|a| * σ / w : ℝ))) : ℂ) = ((|a| : ℝ) : ℂ) * (σ : ℂ) * (w : ℂ)⁻¹ := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, div_eq_mul_inv]
  have h7 : (Real.exp (-(Real.pi * a ^ 2 * σ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ) *
      (Real.exp (-(Real.pi * ((|a| * σ / w) / r) ^ 2)) : ℂ) *
        (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) =
      (Real.exp (-(Real.pi * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹) * σ ^ 2)) : ℂ) *
        (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) := by
    simp only [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    have : (|a| * σ / w / r) ^ 2 = a ^ 2 * σ ^ 2 * ((w * r) ^ 2)⁻¹ := by
      rw [div_div, div_pow, mul_pow, sq_abs]; ring
    rw [this]; ring
  unfold Fc Rc Φc
  rw [h5, h6, h1, h2, h3, h4]
  linear_combination ((σ : ℂ) ^ (z - 1) * C * ((|a| : ℝ) : ℂ) * (σ : ℂ) * (w : ℂ)⁻¹ * 4 * (r : ℂ) ^ p *
    ((|a| : ℝ) : ℂ) ^ q * (σ : ℂ) ^ q * ((w : ℂ) ^ q)⁻¹ * ((r : ℂ) ^ q)⁻¹ * (r : ℂ)⁻¹ * (w : ℂ) ^ κ) * h7

end JForm

namespace JForm

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem integral_Fc_sigma (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) (hzq : -1 < (z + q).re)
    {w r : ℝ} (hw : 0 < w) (hr : 0 < r) :
    ∫ σ in Ioi (0:ℝ), Fc a C p q κ z σ w r =
      (2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) *
        Complex.Gamma ((z + q + 1) / 2)) * Jc' a p q κ z w r := by
  have hB : 0 < Real.pi * a ^ 2 * (1 + ((w * r) ^ 2)⁻¹) := by
    have : 0 < a ^ 2 := by positivity
    positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun σ hσ => Fc_eq a ha C p q κ z (mem_Ioi.1 hσ) hw hr),
    integral_mul_const, integral_cpow_mul_exp_neg_mul_sq _ hB _ hzq, Jc'_eq_mul_Φc,
    cpow_ofReal_mul' (by positivity) (by positivity)]
  ring

theorem integral_Fc_sigma_ae (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) (hzq : -1 < (z + q).re) :
    ∀ᵐ v : ℝ × ℝ ∂((μ0).prod (μ0)),
      ∫ σ in Ioi (0:ℝ), Fc a C p q κ z σ v.1 v.2 =
        (2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) *
          Complex.Gamma ((z + q + 1) / 2)) * Jc a p q κ z v := by
  filter_upwards [MGReal.ae_pos_prod] with v hv
  rw [Jc_eq]
  exact integral_Fc_sigma a ha C p q κ z hzq hv.1 hv.2

theorem mellin_Hc_eq (a : ℝ) (ha : a ≠ 0) (C p q κ z : ℂ) (hzq : -1 < (z + q).re)
    (hzp : -1 < (z + p).re) :
    mellin (Hc a C p q κ) z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ), Jc' a p q κ z w r := by
  have hI := integrable_Fc a ha C p q κ z hzq hzp
  have hae : ∀ᵐ σ : ℝ ∂(μ0), Integrable (fun v : ℝ × ℝ => Fc a C p q κ z σ v.1 v.2) ((μ0).prod (μ0)) :=
    hI.prod_right_ae

  have e1 : mellin (Hc a C p q κ) z = ∫ σ in Ioi (0:ℝ), ∫ v : ℝ × ℝ, Fc a C p q κ z σ v.1 v.2 ∂((μ0).prod (μ0)) := by
    unfold mellin
    refine integral_congr_ae ?_
    filter_upwards [hae] with σ hσ
    rw [mellin_integrand_eq_iter, integral_prod _ hσ]

  have e2 : ∫ σ in Ioi (0:ℝ), ∫ v : ℝ × ℝ, Fc a C p q κ z σ v.1 v.2 ∂((μ0).prod (μ0)) =
      ∫ v : ℝ × ℝ, (∫ σ in Ioi (0:ℝ), Fc a C p q κ z σ v.1 v.2) ∂((μ0).prod (μ0)) :=
    integral_integral_swap hI

  have e3 : ∫ v : ℝ × ℝ, (∫ σ in Ioi (0:ℝ), Fc a C p q κ z σ v.1 v.2) ∂((μ0).prod (μ0)) =
      (2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) *
          Complex.Gamma ((z + q + 1) / 2)) * ∫ v : ℝ × ℝ, Jc a p q κ z v ∂((μ0).prod (μ0)) := by
    rw [integral_congr_ae (integral_Fc_sigma_ae a ha C p q κ z hzq), integral_const_mul]

  have e4 : ∫ v : ℝ × ℝ, Jc a p q κ z v ∂((μ0).prod (μ0)) =
      ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ), Jc' a p q κ z w r :=
    integral_prod _ (integrable_Jc a ha p q κ z hzq hzp)
  rw [e1, e2, e3, e4]

theorem jform (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent H z ∧
    Integrable (fun v : ℝ × ℝ =>
        (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
          (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) ∧
    mellin H z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
          (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) := by
  have hH' : H = Hc a C p q κ := hH
  subst hH'
  exact ⟨mellinConvergent_Hc a ha C p q κ z hzq hzp, integrable_Jc a ha p q κ z hzq hzp,
    mellin_Hc_eq a ha C p q κ z hzq hzp⟩

end JForm

theorem solution
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent H z ∧
    Integrable (fun v : ℝ × ℝ =>
        (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
          (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) ∧
    mellin H z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
          (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) :=
  JForm.jform a ha p q κ C H hH z hzq hzp

end S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
end P2MW
export P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral (solution)
