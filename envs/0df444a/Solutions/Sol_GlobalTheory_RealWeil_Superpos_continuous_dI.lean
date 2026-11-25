-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.continuous_dI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:23.182916+00:00
-- url     : https://prove2.me/submissions/333d31d3-df6d-41e9-b2bc-8fbccaafdbd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_continuous_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_dI_apply
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
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Continuous h) (g : V → B) (v : V) :
    Continuous (dI om ρ ι h g v) := by
  refine continuous_clm_apply.2 fun z => ?_
  simp only [dI_apply]
  exact (continuous_itg hρ (hh.mul (continuous_const.mul
    (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))) g v).add (continuous_itg hρ hh _ v)
end GlobalTheory.RealWeil.Superpos
