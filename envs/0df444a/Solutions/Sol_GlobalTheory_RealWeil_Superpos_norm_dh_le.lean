-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.norm_dh_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:28.688594+00:00
-- url     : https://prove2.me/submissions/9c854f97-42fa-4177-a698-4fcc26554f4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates

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
theorem _root_.solution (h : Y → ℂ) (z : V) (y : Y) :
    ‖dh om ι h z y‖ ≤ 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hhy := norm_nonneg (h y)
  calc ‖h y‖ * (2 * π * ‖om z (ι y)‖) ≤ ‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖))) := by gcongr
    _ = 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by ring
end GlobalTheory.RealWeil.Superpos
