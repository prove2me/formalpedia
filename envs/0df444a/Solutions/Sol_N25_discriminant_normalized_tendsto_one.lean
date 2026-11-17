-- Prove2me | solution 1 for N25.discriminant_normalized_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:34.373439+00:00
-- url     : https://prove2.me/submissions/2dbde5c8-de5f-4c7d-931b-093982ab477c

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_discriminant_normalized_hasSum
import Theorems.Thm_N25_analyticAt_and_qExpansion_of_hasSum

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

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

/-- The discriminant divided by its leading q factor tends to one at the cusp. -/
theorem _root_.solution :
    Filter.Tendsto
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ /
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 1) := by
  let f : UpperHalfPlane → ℂ := fun τ => ModularForm.discriminant τ /
    Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hf (τ : UpperHalfPlane) : HasSum
      (fun n : ℕ => ((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) (f τ) := by
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one, smul_eq_mul] using
      discriminant_normalized_hasSum τ
  have H := analyticAt_and_qExpansion_of_hasSum f ModularCurve.dedekindEtaUnit
    discriminant_normalized_hasSum
  have hz : UpperHalfPlane.cuspFunction 1 f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) H.2
    rw [UpperHalfPlane.qExpansion_coeff] at h
    simpa [PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularCurve.constantCoeff_dedekindEtaUnit] using h
  have he (τ : UpperHalfPlane) :
      UpperHalfPlane.cuspFunction 1 f (Function.Periodic.qParam 1 (τ : ℂ)) = f τ :=
    (cusp_hasSum_punctured hf (Function.Periodic.norm_qParam_lt_one zero_lt_one τ.im_pos)
      (Function.Periodic.qParam_ne_zero _)).unique (hf τ)
  have ht := H.1.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  simpa only [Function.comp_def, he, hz] using ht

end N25
