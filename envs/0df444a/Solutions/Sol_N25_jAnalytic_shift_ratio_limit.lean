-- Prove2me | solution 1 for N25.jAnalytic_shift_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:35.86532+00:00
-- url     : https://prove2.me/submissions/26259275-1484-40e0-b2c0-1f2a40f47ef9

import Mathlib
import Theorems.Thm_N25_jAnalytic_normalized_limit
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

open Filter Topology UpperHalfPlane

namespace N25

/-- The ratio of analytic j-values at a real translate has its exact root-of-unity limit. -/
theorem _root_.solution (b : ℝ) (φ : UpperHalfPlane → UpperHalfPlane)
    (hφ : ∀ τ : UpperHalfPlane, (φ τ : ℂ) = (τ : ℂ) + (b : ℂ)) :
    Tendsto (fun τ : UpperHalfPlane =>
      (ModularForm.E₄ (φ τ) ^ 3 / ModularForm.discriminant (φ τ)) /
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ))
      UpperHalfPlane.atImInfty (nhds (Complex.exp (-(2 * Real.pi * Complex.I * (b : ℂ))))) := by
  have ht : Tendsto φ UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    have he : UpperHalfPlane.im ∘ φ = UpperHalfPlane.im := by
      funext τ
      change (φ τ : ℂ).im = (τ : ℂ).im
      rw [hφ]
      simp
    rw [he]
    exact tendsto_comap
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I * (b : ℂ))
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hs := jAnalytic_normalized_limit.comp ht
  have hd := hs.div jAnalytic_normalized_limit (one_ne_zero : (1 : ℂ) ≠ 0)
  have he (τ : UpperHalfPlane) :
      (Complex.exp (2 * Real.pi * Complex.I * (φ τ : ℂ)) *
        (ModularForm.E₄ (φ τ) ^ 3 / ModularForm.discriminant (φ τ))) /
      (Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) *
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) * w⁻¹ =
      (ModularForm.E₄ (φ τ) ^ 3 / ModularForm.discriminant (φ τ)) /
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
    rw [hφ, mul_add, Complex.exp_add]
    have hq := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))
    change ((_ * w) * _) / (_ * _) * w⁻¹ = _
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp
  have hf := hd.mul_const w⁻¹
  simpa only [Function.comp_def, Pi.div_apply, he, div_self one_ne_zero, one_mul, w, Complex.exp_neg] using hf

end N25
