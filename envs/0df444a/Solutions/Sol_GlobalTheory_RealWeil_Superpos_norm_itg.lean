-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.norm_itg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:53.269141+00:00
-- url     : https://prove2.me/submissions/01e89a7d-1105-45f1-bed9-ada125e2af04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_norm_ph

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
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    ‖itg om ρ ι h g v y‖ = ‖h y‖ * ‖g v‖ := by
  simp [itg, norm_smul, norm_ph, hρ.2.2.1]
end GlobalTheory.RealWeil.Superpos
