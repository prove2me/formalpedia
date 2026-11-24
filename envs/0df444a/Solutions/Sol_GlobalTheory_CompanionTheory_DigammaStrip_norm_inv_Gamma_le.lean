-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaStrip.norm_inv_Gamma_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:16.876682+00:00
-- url     : https://prove2.me/submissions/f3173a48-83fb-4c27-8368-687d0e00c1f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaBoundVerticalStrip
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_norm_sin_le_exp
import Theorems.Thm_PI_EF_norm_Gamma_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaStrip
namespace GlobalTheory.CompanionTheory.DigammaStrip
theorem _root_.solution {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) (h3 : 1 / 4 ≤ |w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 16 * K * Real.exp (Real.pi * |w.im|) := by
  have hw0 : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at h3
    norm_num at h3
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have := congrArg Complex.im hk
    exact hw0 (by simpa using this)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
    have h6 : Complex.Gamma w * Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) = Real.pi := by
      rw [hrefl, div_mul_cancel₀ _ hsin]
    refine eq_div_of_mul_eq hpi ?_
    rw [inv_mul_eq_iff_eq_mul₀ hG]
    linear_combination -h6
  have hn1 : (1 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hn2 : (2 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hrec : Complex.Gamma (3 - w) = (2 - w) * ((1 - w) * Complex.Gamma (1 - w)) := by
    have e1 := Complex.Gamma_add_one (1 - w) hn1
    have e2 := Complex.Gamma_add_one (2 - w) hn2
    rw [show (2 - w) + 1 = 3 - w by ring] at e2
    rw [show (1 - w) + 1 = 2 - w by ring] at e1
    rw [e2, e1]
  have hb1 : 1 / 4 ≤ ‖1 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have hb2 : 1 / 4 ≤ ‖2 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (2 - w)
    simpa using this
  have hre3 : (3 - w).re = 3 - w.re := by simp
  have hG3 : ‖Complex.Gamma (3 - w)‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by rw [hre3]; linarith)).trans
      (hK _ (by rw [hre3]; linarith) (by rw [hre3]; linarith))
  have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 16 * K := by
    rw [hrec, norm_mul, norm_mul] at hG3
    have hp := norm_nonneg (Complex.Gamma (1 - w))
    have : (1 / 4) * ((1 / 4) * ‖Complex.Gamma (1 - w)‖) ≤
        ‖2 - w‖ * (‖1 - w‖ * ‖Complex.Gamma (1 - w)‖) := by gcongr
    linarith
  have hs : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [div_le_iff₀ Real.pi_pos]
  have he := Real.exp_pos (Real.pi * |w.im|)
  calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖
      ≤ (16 * K) * Real.exp (Real.pi * |w.im|) := by gcongr
    _ = 16 * K * Real.exp (Real.pi * |w.im|) * 1 := by ring
    _ ≤ 16 * K * Real.exp (Real.pi * |w.im|) * Real.pi := by gcongr
end GlobalTheory.CompanionTheory.DigammaStrip
