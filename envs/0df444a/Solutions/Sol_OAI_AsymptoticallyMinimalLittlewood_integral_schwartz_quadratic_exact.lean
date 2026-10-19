-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:09:36.332575+00:00
-- url     : https://prove2.me/submissions/7d999093-7ac4-4f78-a8cf-c8e12eb08ff6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Gaussian.lean:L154-L180
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_integral_schwartz_mul_gaussian_boundary

-- ---- from OAI.Analysis.Littlewood.Gaussian ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Quadratic Fourier identity with an undamped, nonzero real curvature. -/
theorem integral_schwartz_quadratic_exact (f : 𝓢(ℝ, ℂ))
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
    1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-Real.pi / t * (ξ + u) ^ 2) := by
  have hb0 : -Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
  have hb : 0 ≤ (-Complex.I * (t : ℂ)).re := by simp
  convert integral_schwartz_mul_gaussian_boundary f hb hb0 u using 1
  · apply integral_congr_ae
    filter_upwards with x
    congr 1
    unfold realPhase
    congr 1
    push_cast
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    congr 1
    unfold realPhase
    congr 1
    push_cast
    field_simp
    simp [Complex.I_sq]
    ring

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact := @_root_.OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact
