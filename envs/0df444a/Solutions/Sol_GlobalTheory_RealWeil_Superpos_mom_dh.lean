-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.mom_dh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:34.909255+00:00
-- url     : https://prove2.me/submissions/99c15fda-3156-4e18-8acf-9daa4d6b9cd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
open GlobalTheory.RealWeil.Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution {h : Y → ℂ} (hh : Mom ν h) (z : V) : Mom ν (dh om ι h z) := by
  refine ⟨hh.1.mul (continuous_const.mul (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous))),
    fun n => ?_⟩
  refine Integrable.mono' ((hh.2 (n + 1)).const_mul (2 * π * ‖om‖ * ‖z‖ * ‖ι‖))
    ((continuous_norm.pow n).mul (continuous_norm.comp (hh.1.mul (continuous_const.mul
      (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [Real.norm_of_nonneg (by positivity), dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hy := norm_nonneg y
  have hhy := norm_nonneg (h y)
  calc ‖y‖ ^ n * (‖h y‖ * (2 * π * ‖om z (ι y)‖)) ≤ ‖y‖ ^ n * (‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖)))) := by
        gcongr
    _ = 2 * π * ‖om‖ * ‖z‖ * ‖ι‖ * (‖y‖ ^ (n + 1) * ‖h y‖) := by ring
end GlobalTheory.RealWeil.Superpos
