-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:14:50.282045+00:00
-- url     : https://prove2.me/submissions/87ede3e4-c1e4-4e40-a628-07d2e3967788

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Gaussian.lean:L320-L348
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_uniform_quadratic_error

-- ---- from OAI.Analysis.Littlewood.Gaussian ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- The argument of the nonzero imaginary curvature, on the principal branch. -/
theorem arg_negative_imaginary {t : ℝ} (ht : t ≠ 0) :
    Complex.arg (-Complex.I * (t : ℂ)) = -Real.sign t * Real.pi / 2 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have heq : -Complex.I * (t : ℂ) = Complex.I * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.arg_mul_real (neg_pos.mpr ht), Complex.arg_I,
      Real.sign_of_neg ht]
    ring
  · rw [Complex.arg_mul_real ht, Complex.arg_neg_I, Real.sign_of_pos ht]
    ring

theorem quadratic_prefactor_eq {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ)) *
        realPhase (-Real.pi / t * u ^ 2) =
      realPhase (Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t) /
        (Real.sqrt |t| : ℂ) := by
  have he : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by norm_num
  rw [one_div, ← Complex.cpow_neg, he, Complex.cpow_ofReal]
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg (abs_nonneg t), ← Real.sqrt_eq_rpow, arg_negative_imaginary ht]
  have harg : (-Real.sign t * Real.pi / 2) * (-(1 / 2)) =
      Real.pi * Real.sign t / 4 := by ring
  rw [harg]
  have hphase (x : ℝ) : (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I = realPhase x := by
    unfold realPhase
    rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hphase]
  rw [mul_assoc, ← realPhase_add]
  have heq : Real.pi * Real.sign t / 4 + -Real.pi / t * u ^ 2 =
      Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t := by ring
  rw [heq]
  push_cast
  ring

theorem uniform_quadratic_integration (g : ℝ → ℂ) (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {β : ℝ} (hβ : β ≠ 0) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ (Real.pi / |β| * (∫ ξ : ℝ, ξ ^ 2 *
        ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ, ℂ)) ξ‖)) / T ∧
      (∫ x : ℝ, g x * realPhase (2 * Real.pi * (T * β * x ^ 2 / 2 - u * x))) =
        (realPhase (2 * Real.pi * (Real.sign β / 8 - u ^ 2 / (2 * T * β))) /
          (Real.sqrt (T * |β|) : ℂ)) * (g (u / (T * β)) + E) := by
  obtain ⟨E, hE, hEq⟩ := uniform_quadratic_error (hg.toSchwartzMap hgs)
    (mul_ne_zero hT.ne' hβ) u
  refine ⟨E, ?_, ?_⟩
  · convert hE using 1
    rw [abs_mul, abs_of_pos hT]
    ring
  · rw [quadratic_prefactor_eq (mul_ne_zero hT.ne' hβ)] at hEq
    have hs : Real.sign (T * β) = Real.sign β := by
      rcases lt_or_gt_of_ne hβ with hβ | hβ
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hT hβ), Real.sign_of_neg hβ]
      · rw [Real.sign_of_pos (mul_pos hT hβ), Real.sign_of_pos hβ]
    have hnorm : |T * β| = T * |β| := by rw [abs_mul, abs_of_pos hT]
    simp only [hs, hnorm, HasCompactSupport.toSchwartzMap] at hEq
    convert hEq using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    · congr 2
      congr 1
      ring

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration := @_root_.OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration
