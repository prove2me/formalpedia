-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1a251a3c-f990-5a5e-88fc-66ae0f96ad32

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace K7GV

theorem abs_log_le {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ |t - 1| + |t⁻¹ - 1| := by
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
  have h2 : -Real.log t ≤ t⁻¹ - 1 := by
    rw [← Real.log_inv]; exact Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [abs_le]; constructor
  · have := le_abs_self (t⁻¹ - 1); have := abs_nonneg (t - 1); linarith
  · have := le_abs_self (t - 1); have := abs_nonneg (t⁻¹ - 1); linarith

theorem norm_cexp_I_mul_sub_one_le (x : ℝ) : ‖Complex.exp (Complex.I * x) - 1‖ ≤ |x| := by
  have e : Complex.exp (Complex.I * x) - 1 = ((Real.cos x - 1 : ℝ) : ℂ) + (Real.sin x : ℝ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
  rw [e, Complex.norm_add_mul_I]
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.sin_sq_add_cos_sq x
  have h2 : (Real.cos x - 1) ^ 2 + Real.sin x ^ 2 ≤ x ^ 2 := by nlinarith
  calc Real.sqrt ((Real.cos x - 1) ^ 2 + Real.sin x ^ 2) ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt h2
    _ = |x| := Real.sqrt_sq_eq_abs x

theorem norm_cexp_I_mul_sub_le (a c : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * c)‖ ≤ |a - c| := by
  have : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * c) =
      Complex.exp (Complex.I * c) * (Complex.exp (Complex.I * ((a - c : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact norm_cexp_I_mul_sub_one_le (a - c)

theorem abs_le_amgm (u l : ℝ) (hl : 0 < l) : |u| ≤ l / 2 + u ^ 2 / (2 * l) := by
  have : 0 ≤ (|u| - l) ^ 2 / (2 * l) := by positivity
  have e : (|u| - l) ^ 2 / (2 * l) = u ^ 2 / (2 * l) - |u| + l / 2 := by rw [sub_sq, sq_abs]; field_simp
  linarith

noncomputable def ψ (σ t : ℝ) : ℝ := Real.exp (-t) * t ^ (σ - 1)

theorem ψ_pos (σ : ℝ) {t : ℝ} (ht : 0 < t) : 0 < ψ σ t := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _)

theorem integrableOn_ψ {σ : ℝ} (hσ : 0 < σ) : IntegrableOn (ψ σ) (Ioi 0) := Real.GammaIntegral_convergent hσ

theorem integral_ψ {σ : ℝ} (hσ : 0 < σ) : ∫ t in Ioi (0 : ℝ), ψ σ t = Real.Gamma σ := (Real.Gamma_eq_integral hσ).symm

theorem ψ_mul_pow (σ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) : ψ σ t * t ^ k = ψ (σ + k) t := by
  rw [ψ, ψ, show σ + k - 1 = (σ - 1) + (k : ℕ) by push_cast; ring, Real.rpow_add ht, Real.rpow_natCast]; ring

theorem ψ_mul_inv_pow (σ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) : ψ σ t * (t ^ k)⁻¹ = ψ (σ - k) t := by
  rw [ψ, ψ, show σ - k - 1 = (σ - 1) + (-(k : ℝ)) by ring, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_natCast]; ring

theorem quad_up {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (hc : c ≠ 0) :
    IntegrableOn (fun t : ℝ => ψ σ t * (t / c - 1) ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ψ σ t * (t / c - 1) ^ 2 =
      Real.Gamma (σ + 2) / c ^ 2 - 2 * Real.Gamma (σ + 1) / c + Real.Gamma σ := by
  have i0 := integrableOn_ψ hσ
  have ip : ∀ k : ℕ, IntegrableOn (fun t : ℝ => ψ σ t * t ^ k) (Ioi 0) := fun k =>
    (integrableOn_ψ (by positivity : 0 < σ + k)).congr_fun (fun t ht => (ψ_mul_pow σ k ht).symm) measurableSet_Ioi
  have hk : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), ψ σ t * t ^ k = Real.Gamma (σ + k) := fun k => by
    rw [← integral_ψ (by positivity : 0 < σ + k)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => ψ_mul_pow σ k ht)
  have e : ∀ t : ℝ, ψ σ t * (t / c - 1) ^ 2 = c⁻¹ ^ 2 * (ψ σ t * t ^ 2) - 2 * c⁻¹ * (ψ σ t * t ^ 1) + ψ σ t := by
    intro t; rw [div_eq_mul_inv]; ring
  have j2 : Integrable (fun t : ℝ => c⁻¹ ^ 2 * (ψ σ t * t ^ 2)) (volume.restrict (Ioi 0)) := (ip 2).const_mul _
  have j1 : Integrable (fun t : ℝ => 2 * c⁻¹ * (ψ σ t * t ^ 1)) (volume.restrict (Ioi 0)) := (ip 1).const_mul _
  have j21 : Integrable (fun t : ℝ => c⁻¹ ^ 2 * (ψ σ t * t ^ 2) - 2 * c⁻¹ * (ψ σ t * t ^ 1)) (volume.restrict (Ioi 0)) := j2.sub j1
  simp_rw [e]
  refine ⟨j21.add i0, ?_⟩
  rw [integral_add j21 i0, integral_sub j2 j1, integral_const_mul, integral_const_mul, hk 2, hk 1, integral_ψ hσ]
  push_cast; field_simp

theorem quad_down {σ : ℝ} (hσ : 2 < σ) (c : ℝ) :
    IntegrableOn (fun t : ℝ => ψ σ t * (c / t - 1) ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ψ σ t * (c / t - 1) ^ 2 =
      c ^ 2 * Real.Gamma (σ - 2) - 2 * c * Real.Gamma (σ - 1) + Real.Gamma σ := by
  have i0 := integrableOn_ψ (by linarith : 0 < σ)
  have im : ∀ k : ℕ, (k : ℝ) < σ → IntegrableOn (fun t : ℝ => ψ σ t * (t ^ k)⁻¹) (Ioi 0) := fun k hk =>
    (integrableOn_ψ (by linarith : 0 < σ - k)).congr_fun (fun t ht => (ψ_mul_inv_pow σ k ht).symm) measurableSet_Ioi
  have hk : ∀ k : ℕ, (k : ℝ) < σ → ∫ t in Ioi (0 : ℝ), ψ σ t * (t ^ k)⁻¹ = Real.Gamma (σ - k) := fun k hk => by
    rw [← integral_ψ (by linarith : 0 < σ - k)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => ψ_mul_inv_pow σ k ht)
  have e : ∀ t ∈ Ioi (0 : ℝ), ψ σ t * (c / t - 1) ^ 2 =
      c ^ 2 * (ψ σ t * (t ^ 2)⁻¹) - 2 * c * (ψ σ t * (t ^ 1)⁻¹) + ψ σ t := by
    intro t ht; have : t ≠ 0 := ne_of_gt ht; field_simp; ring
  have j2 : Integrable (fun t : ℝ => c ^ 2 * (ψ σ t * (t ^ 2)⁻¹)) (volume.restrict (Ioi 0)) := (im 2 (by norm_num; linarith)).const_mul _
  have j1 : Integrable (fun t : ℝ => 2 * c * (ψ σ t * (t ^ 1)⁻¹)) (volume.restrict (Ioi 0)) := (im 1 (by norm_num; linarith)).const_mul _
  have j21 : Integrable (fun t : ℝ => c ^ 2 * (ψ σ t * (t ^ 2)⁻¹) - 2 * c * (ψ σ t * (t ^ 1)⁻¹)) (volume.restrict (Ioi 0)) := j2.sub j1
  have hint : IntegrableOn (fun t : ℝ => c ^ 2 * (ψ σ t * (t ^ 2)⁻¹) - 2 * c * (ψ σ t * (t ^ 1)⁻¹) + ψ σ t) (Ioi 0) := j21.add i0
  refine ⟨hint.congr_fun (fun t ht => (e t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add j21 i0, integral_sub j2 j1, integral_const_mul, integral_const_mul,
    hk 2 (by norm_num; linarith), hk 1 (by norm_num; linarith), integral_ψ (by linarith)]
  push_cast; ring

theorem cpow_polar (σ τ : ℝ) {t : ℝ} (ht : 0 < t) :
    ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (((σ : ℂ) + (τ : ℂ) * Complex.I) - 1) =
      ((ψ σ t : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ * Real.log t : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), ← Complex.ofReal_log ht.le,
    show (Real.log t : ℂ) * (((σ : ℂ) + (τ : ℂ) * Complex.I) - 1) = (((σ - 1) * Real.log t : ℝ) : ℂ) + Complex.I * ((τ * Real.log t : ℝ) : ℂ) by
      push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, ψ, Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
  push_cast; ring

theorem coherence (σ τ w₀ l : ℝ) (hσ : 2 < σ) (hw₀ : 0 < w₀) (hl : 0 < l) :
    Real.Gamma σ - |τ| * (l * Real.Gamma σ +
      ((Real.Gamma (σ + 2) / w₀ ^ 2 - 2 * Real.Gamma (σ + 1) / w₀ + Real.Gamma σ) +
       (w₀ ^ 2 * Real.Gamma (σ - 2) - 2 * w₀ * Real.Gamma (σ - 1) + Real.Gamma σ)) / (2 * l))
      ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
  have hσ0 : 0 < σ := by linarith
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : 0 < s.re := by rw [hs]; simp; exact hσ0
  rw [Complex.Gamma_eq_integral hsre, Complex.GammaIntegral]
  set P₀ : ℂ := Complex.exp (Complex.I * ((τ * Real.log w₀ : ℝ) : ℂ)) with hP₀
  have hP₀n : ‖P₀‖ = 1 := by rw [hP₀]; exact Complex.norm_exp_I_mul_ofReal _
  have hΓ := Real.Gamma_pos_of_pos hσ0
  have hKint : ∫ t in Ioi (0 : ℝ), ((ψ σ t : ℝ) : ℂ) = ((Real.Gamma σ : ℝ) : ℂ) := by
    rw [← integral_ψ hσ0, ← integral_complex_ofReal]
  have hi1 : IntegrableOn (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1)) (Ioi 0) :=
    Complex.GammaIntegral_convergent hsre
  have hi2 : IntegrableOn (fun t : ℝ => P₀ * ((ψ σ t : ℝ) : ℂ)) (Ioi 0) := ((integrableOn_ψ hσ0).ofReal).const_mul P₀
  have hdiff : (∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1)) - P₀ * ((Real.Gamma σ : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), (((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1) - P₀ * ((ψ σ t : ℝ) : ℂ)) := by
    rw [integral_sub hi1 hi2, integral_const_mul, hKint]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1) - P₀ * ((ψ σ t : ℝ) : ℂ)‖ ≤
      |τ| * l * ψ σ t + |τ| / (2 * l) * (ψ σ t * (t / w₀ - 1) ^ 2) + |τ| / (2 * l) * (ψ σ t * (w₀ / t - 1) ^ 2) := by
    intro t ht
    have ht : 0 < t := ht
    rw [hs, cpow_polar σ τ ht, hP₀, mul_comm (Complex.exp _) (((ψ σ t : ℝ) : ℂ)), ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (ψ_pos σ ht)]
    have h1 : ‖Complex.exp (Complex.I * ((τ * Real.log t : ℝ) : ℂ)) - Complex.exp (Complex.I * ((τ * Real.log w₀ : ℝ) : ℂ))‖
        ≤ |τ| * (|t / w₀ - 1| + |w₀ / t - 1|) := by
      refine (norm_cexp_I_mul_sub_le _ _).trans ?_
      rw [← mul_sub, abs_mul, ← Real.log_div ht.ne' hw₀.ne']
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_log_le (div_pos ht hw₀)
      rwa [inv_div] at this
    have h2 := abs_le_amgm (t / w₀ - 1) l hl
    have h3 := abs_le_amgm (w₀ / t - 1) l hl
    have hφ := ψ_pos σ ht
    have hy := abs_nonneg τ
    calc ψ σ t * ‖Complex.exp (Complex.I * ((τ * Real.log t : ℝ) : ℂ)) - Complex.exp (Complex.I * ((τ * Real.log w₀ : ℝ) : ℂ))‖
        ≤ ψ σ t * (|τ| * (|t / w₀ - 1| + |w₀ / t - 1|)) := mul_le_mul_of_nonneg_left h1 hφ.le
      _ ≤ ψ σ t * (|τ| * ((l / 2 + (t / w₀ - 1) ^ 2 / (2 * l)) + (l / 2 + (w₀ / t - 1) ^ 2 / (2 * l)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add h2 h3) hy) hφ.le
      _ = _ := by ring
  obtain ⟨iA, hA⟩ := quad_up hσ0 w₀ hw₀.ne'
  obtain ⟨iB, hB⟩ := quad_down hσ w₀
  have i0 := integrableOn_ψ hσ0
  have j0 : Integrable (fun t : ℝ => |τ| * l * ψ σ t) (volume.restrict (Ioi 0)) := i0.const_mul _
  have jA : Integrable (fun t : ℝ => |τ| / (2 * l) * (ψ σ t * (t / w₀ - 1) ^ 2)) (volume.restrict (Ioi 0)) := iA.const_mul _
  have jB : Integrable (fun t : ℝ => |τ| / (2 * l) * (ψ σ t * (w₀ / t - 1) ^ 2)) (volume.restrict (Ioi 0)) := iB.const_mul _
  have j0A : Integrable (fun t : ℝ => |τ| * l * ψ σ t + |τ| / (2 * l) * (ψ σ t * (t / w₀ - 1) ^ 2)) (volume.restrict (Ioi 0)) := j0.add jA
  have hrhs : IntegrableOn (fun t : ℝ => |τ| * l * ψ σ t + |τ| / (2 * l) * (ψ σ t * (t / w₀ - 1) ^ 2) +
      |τ| / (2 * l) * (ψ σ t * (w₀ / t - 1) ^ 2)) (Ioi 0) := j0A.add jB
  have hI : ‖(∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1)) - P₀ * ((Real.Gamma σ : ℝ) : ℂ)‖ ≤
      |τ| * (l * Real.Gamma σ + ((Real.Gamma (σ + 2) / w₀ ^ 2 - 2 * Real.Gamma (σ + 1) / w₀ + Real.Gamma σ) +
        (w₀ ^ 2 * Real.Gamma (σ - 2) - 2 * w₀ * Real.Gamma (σ - 1) + Real.Gamma σ)) / (2 * l)) := by
    rw [hdiff]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_on (hi1.sub hi2).norm hrhs measurableSet_Ioi hpt).trans (le_of_eq ?_)
    rw [integral_add j0A jB, integral_add j0 jA, integral_const_mul, integral_const_mul, integral_const_mul, hA, hB, integral_ψ hσ0]
    field_simp
    ring
  have hK : ‖P₀ * ((Real.Gamma σ : ℝ) : ℂ)‖ = Real.Gamma σ := by
    rw [norm_mul, hP₀n, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΓ]
  have := norm_sub_norm_le (P₀ * ((Real.Gamma σ : ℝ) : ℂ)) (∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1))
  rw [hK, norm_sub_rev] at this
  linarith

theorem norm_Gamma_le (σ τ : ℝ) (hσ : 0 < σ) : ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : 0 < s.re := by rw [hs]; simp; exact hσ
  rw [Complex.Gamma_eq_integral hsre, Complex.GammaIntegral, ← integral_ψ hσ]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 0 < t) => ?_)
  rw [hs, cpow_polar σ τ ht, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ψ_pos σ ht)]

end K7GV

theorem solution
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ σ τ : ℝ, R ≤ σ → |τ| ≤ K →
      (1 - ε) * Real.Gamma σ ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by
  set l : ℝ := ε / (2 * (K + 1)) with hl
  have hl0 : 0 < l := by rw [hl]; positivity
  refine ⟨max 4 (18 * (K + 1) ^ 2 / ε ^ 2), fun σ τ hσ hτ => ?_⟩
  have hσ4 : 4 ≤ σ := le_trans (le_max_left _ _) hσ
  have hσR : 18 * (K + 1) ^ 2 / ε ^ 2 ≤ σ := le_trans (le_max_right _ _) hσ
  have hσ2 : 2 < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨?_, K7GV.norm_Gamma_le σ τ hσ0⟩
  have hcoh := K7GV.coherence σ τ σ l hσ2 hσ0 hl0

  set g : ℝ := Real.Gamma (σ - 2) with hg
  have hgpos : 0 < g := Real.Gamma_pos_of_pos (by linarith)
  have e1 : Real.Gamma (σ - 1) = (σ - 2) * g := by
    rw [hg, show σ - 1 = (σ - 2) + 1 by ring, Real.Gamma_add_one (by linarith)]
  have e0 : Real.Gamma σ = (σ - 1) * ((σ - 2) * g) := by
    rw [← e1, show (σ : ℝ) = (σ - 1) + 1 by ring, Real.Gamma_add_one (by linarith)]; ring_nf
  have ep1 : Real.Gamma (σ + 1) = σ * ((σ - 1) * ((σ - 2) * g)) := by
    rw [← e0, Real.Gamma_add_one hσ0.ne']
  have ep2 : Real.Gamma (σ + 2) = (σ + 1) * (σ * ((σ - 1) * ((σ - 2) * g))) := by
    rw [← ep1, show σ + 2 = (σ + 1) + 1 by ring, Real.Gamma_add_one (by linarith)]
  have hΓ : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσ0

  have hA : Real.Gamma (σ + 2) / σ ^ 2 - 2 * Real.Gamma (σ + 1) / σ + Real.Gamma σ = ((σ - 1) * (σ - 2) * g) / σ := by
    rw [ep2, ep1, e0]; field_simp; ring
  have hB : σ ^ 2 * Real.Gamma (σ - 2) - 2 * σ * Real.Gamma (σ - 1) + Real.Gamma σ = (σ + 2) * g := by
    rw [← hg, e1, e0]; ring
  rw [hA, hB] at hcoh

  have hAB : ((σ - 1) * (σ - 2) * g) / σ + (σ + 2) * g ≤ 9 * ((σ - 1) * ((σ - 2) * g)) / σ := by
    rw [div_add' _ _ _ hσ0.ne', div_le_div_iff_of_pos_right hσ0]
    nlinarith
  have hK1 : |τ| ≤ K := hτ
  have hKp : 0 ≤ K := hK

  have h1 : |τ| * (l * Real.Gamma σ) ≤ ε / 2 * Real.Gamma σ := by
    have : |τ| * l ≤ ε / 2 := by
      rw [hl]
      have : |τ| * (ε / (2 * (K + 1))) = (|τ| / (K + 1)) * (ε / 2) := by field_simp
      rw [this]
      have hq : |τ| / (K + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      nlinarith [hε.le]
    nlinarith

  have h2 : |τ| * ((((σ - 1) * (σ - 2) * g) / σ + (σ + 2) * g) / (2 * l)) ≤ ε / 2 * Real.Gamma σ := by
    have hnum : (((σ - 1) * (σ - 2) * g) / σ + (σ + 2) * g) / (2 * l) ≤ (9 * ((σ - 1) * ((σ - 2) * g)) / σ) / (2 * l) :=
      div_le_div_of_nonneg_right hAB (by positivity)
    have hstep : |τ| * ((9 * ((σ - 1) * ((σ - 2) * g)) / σ) / (2 * l)) ≤ ε / 2 * ((σ - 1) * ((σ - 2) * g)) := by

      have hG : 0 < (σ - 1) * ((σ - 2) * g) := by rw [← e0]; exact hΓ
      rw [hl]
      have key : K * 9 * (K + 1) ≤ ε ^ 2 / 2 * σ := by
        have : 18 * (K + 1) ^ 2 ≤ σ * ε ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at hσR; linarith
        nlinarith
      have eq : |τ| * (9 * ((σ - 1) * ((σ - 2) * g)) / σ / (2 * (ε / (2 * (K + 1))))) =
          (|τ| * 9 * (K + 1) / (ε * σ)) * ((σ - 1) * ((σ - 2) * g)) := by field_simp
      rw [eq]
      refine mul_le_mul_of_nonneg_right ?_ hG.le
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg τ]
    calc |τ| * ((((σ - 1) * (σ - 2) * g) / σ + (σ + 2) * g) / (2 * l))
        ≤ |τ| * ((9 * ((σ - 1) * ((σ - 2) * g)) / σ) / (2 * l)) := mul_le_mul_of_nonneg_left hnum (abs_nonneg τ)
      _ ≤ ε / 2 * ((σ - 1) * ((σ - 2) * g)) := hstep
      _ = ε / 2 * Real.Gamma σ := by rw [e0]
  have : |τ| * (l * Real.Gamma σ + (((σ - 1) * (σ - 2) * g) / σ + (σ + 2) * g) / (2 * l)) ≤ ε * Real.Gamma σ := by
    rw [mul_add]; linarith
  linarith

#print axioms solution

end S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le (solution)
