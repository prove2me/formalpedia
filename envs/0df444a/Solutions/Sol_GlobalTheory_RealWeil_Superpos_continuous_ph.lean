-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.continuous_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:18.531962+00:00
-- url     : https://prove2.me/submissions/8b4f2c58-bbf4-4dbd-ae19-f8cb97a70618

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
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) : Continuous (ph om ι v) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ((om v).continuous.comp ι.continuous)))
end GlobalTheory.RealWeil.Superpos
