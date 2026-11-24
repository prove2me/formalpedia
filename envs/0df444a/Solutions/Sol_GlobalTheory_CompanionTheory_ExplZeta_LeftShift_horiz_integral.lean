-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:10.161055+00:00
-- url     : https://prove2.me/submissions/1e3e2783-5d2b-4407-b43c-0aeb9741f0d0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_integral_exp_quarter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift
namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift
theorem _root_.solution {f : ℝ → ℂ} {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h : ∀ σ : ℝ, -R ≤ σ → σ ≤ -(1 / 2) → ‖f σ‖ ≤ 4 * A * Real.exp (σ / 4)) :
    ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f σ‖ ≤ 16 * A := by
  have hle : (-R) ≤ (-(1 / 2) : ℝ) := by linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
    (g := fun σ => 4 * A * Real.exp (σ / 4)) hle
    (Eventually.of_forall fun σ hσ => h σ hσ.1.le hσ.2)
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 4))
      ).intervalIntegrable _ _)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_quarter]
  have e1 : Real.exp (-(1 / 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e2 := Real.exp_pos (-R / 4)
  nlinarith
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
