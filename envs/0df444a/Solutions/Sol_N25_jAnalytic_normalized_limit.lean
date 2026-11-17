-- Prove2me | solution 1 for N25.jAnalytic_normalized_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:35.156063+00:00
-- url     : https://prove2.me/submissions/26f59d09-7ee7-48b8-9323-deb58819b887

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Theorems.Thm_N25_analyticAt_and_qExpansion_of_hasSum
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open Filter Topology Function Complex UpperHalfPlane

namespace N25

private theorem cusp_hasSum_punctured {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : UpperHalfPlane,
      HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun m => c m • q ^ m) (UpperHalfPlane.cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one zero_lt_one hq hq0
  let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ UpperHalfPlane.ofComplex) hq0
  have he : UpperHalfPlane.cuspFunction 1 f q = f τ := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1] using! h2
  grind [hf τ, Function.Periodic.qParam_right_inv]

/-- The analytic j-function has the exact leading coefficient one at imaginary infinity. -/
theorem _root_.solution :
    Tendsto (fun τ : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) *
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ))
      UpperHalfPlane.atImInfty (nhds 1) := by
  let f : UpperHalfPlane → ℂ := fun τ =>
    Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) *
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
  have hf0 (τ : UpperHalfPlane) : HasSum
      (fun n : ℕ => ((PowerSeries.coeff n ModularCurve.jNum : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n) (f τ) := by
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one] using
      ModularCurve.hasSum_jNum_qParam τ
  have hf (τ : UpperHalfPlane) : HasSum
      (fun n : ℕ => ((PowerSeries.coeff n ModularCurve.jNum : ℤ) : ℂ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) (f τ) := by
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one, smul_eq_mul] using hf0 τ
  have H := N25.analyticAt_and_qExpansion_of_hasSum f ModularCurve.jNum hf0
  have hz : UpperHalfPlane.cuspFunction 1 f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) H.2
    rw [UpperHalfPlane.qExpansion_coeff] at h
    simpa [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ModularCurve.constantCoeff_jNum] using h
  have he (τ : UpperHalfPlane) :
      UpperHalfPlane.cuspFunction 1 f (Function.Periodic.qParam 1 (τ : ℂ)) = f τ :=
    (cusp_hasSum_punctured hf (Function.Periodic.norm_qParam_lt_one zero_lt_one τ.im_pos)
      (Function.Periodic.qParam_ne_zero _)).unique (hf τ)
  have ht := H.1.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  simpa only [Function.comp_def, he, hz] using ht

end N25
