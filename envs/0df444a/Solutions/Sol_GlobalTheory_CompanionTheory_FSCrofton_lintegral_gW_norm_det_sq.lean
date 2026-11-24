-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:42.829282+00:00
-- url     : https://prove2.me/submissions/f9e3affd-90ed-4aa9-bfe8-233300ad8199

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_fR_complex
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_fR_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory.CompanionTheory.FSCrofton.GaussDet
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution (d : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (G : Matrix β (Fin d) ℂ) :
    ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
        (G.conjTranspose * G).det.re) := by
  have hint : Integrable (fR G) := by
    have := (integrable_fR_complex G).re
    simpa using this
  have hnn : 0 ≤ᵐ[volume] fR G := ae_of_all _ fun C => by
    simp only [fR, Pi.zero_apply]
    positivity
  have hval : ∫ C, fR G C = Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re := by
    have h := integral_fR_complex G
    rw [integral_complex_ofReal] at h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re] at h2
    rw [h2, pow_mul' ]
    have : ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) =
        (((Real.pi ^ Fintype.card β) ^ d * (d.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, Complex.re_ofReal_mul]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr fun C => ?_
  rw [gW, fR, ENNReal.ofReal_mul (Real.exp_pos _).le]
end GlobalTheory.CompanionTheory.FSCrofton
