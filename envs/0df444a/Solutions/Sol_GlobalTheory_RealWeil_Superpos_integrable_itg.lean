-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.integrable_itg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:11.366814+00:00
-- url     : https://prove2.me/submissions/99899fbf-c3ac-4a19-ac92-f8f99d3ee790

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_continuous_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_norm_itg

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
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) (g : V → B) (v : V) :
    Integrable (itg om ρ ι h g v) ν := by
  refine Integrable.mono' ((hh.2 0).mul_const ‖g v‖) (continuous_itg hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_itg hρ]; simp
end GlobalTheory.RealWeil.Superpos
