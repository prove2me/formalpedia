-- Prove2me | solution 1 for GlobalTheory.HeckeMellin.gamma_integral_exp_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:46.874584+00:00
-- url     : https://prove2.me/submissions/70137787-4dca-4587-89ae-b586a67e1f2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine
import Theorems.Thm_GlobalTheory_HeckeMellin_integrableOn_cpow_mul_exp_neg_mul
import Theorems.Thm_GlobalTheory_HeckeMellin_exp_smul_integrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
open Set
namespace GlobalTheory.HeckeMellin
theorem _root_.solution :
    ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  intro r hr w hw
  set c : ℝ := 2 * Real.pi * r with hcdef
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x)) with hg
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := fun x _ y _ h => Real.exp_injective h
  have hfun : (fun t : ℝ => |Real.exp t| • g (Real.exp t)) =
      fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
    funext t
    exact exp_smul_integrand w c t
  constructor
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj g).mp
      (by rw [himg]; exact integrableOn_cpow_mul_exp_neg_mul hw hc)
    rw [hfun, integrableOn_univ] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [himg, hfun, Measure.restrict_univ] at h2
    rw [← h2, hg, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hc, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, mul_comm]
end GlobalTheory.HeckeMellin
