-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.norm_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:29.84246+00:00
-- url     : https://prove2.me/submissions/3ed71c55-fc4d-45f6-9f94-dd120fbb84e8

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
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ‖ph om ι v y‖ = 1 := by
  unfold ph
  rw [show (2 * π * I * (om v (ι y) : ℂ)) = ((2 * π * om v (ι y) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _
end GlobalTheory.RealWeil.Superpos
