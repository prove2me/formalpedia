-- Prove2me | solution 1 for GlobalTheory.T.heisenberg_smooth_rapid_superposition_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:37.845263+00:00
-- url     : https://prove2.me/submissions/0ea466a2-3c08-4f7d-9bf7-d48e517375f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslatesStatement
import Theorems.Thm_GlobalTheory_RealWeil_sm_superpos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by
  first | exact @GlobalTheory.RealWeil.sm_superpos | exact GlobalTheory.RealWeil.sm_superpos | (intros; apply GlobalTheory.RealWeil.sm_superpos <;> assumption)
end _root_.GlobalTheory.T
