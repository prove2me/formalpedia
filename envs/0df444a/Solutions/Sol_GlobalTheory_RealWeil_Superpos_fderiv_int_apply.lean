-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.fderiv_int_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:37.289435+00:00
-- url     : https://prove2.me/submissions/7028f212-2a1c-484b-8f2e-ff674e1289fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_integrable_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_mom_dh
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_dI_apply
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_continuous_dI
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_exists_bound
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_hasFDerivAt_int

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
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v z : V) :
    fderiv ℝ (fun v => ∫ y, itg om ρ ι h g v y ∂ν) v z =
      (∫ y, itg om ρ ι (dh om ι h z) g v y ∂ν) + ∫ y, itg om ρ ι h (fun w => fderiv ℝ g w z) v y ∂ν := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v
  have hi : Integrable (dI om ρ ι h g v) ν := hbd.mono' (continuous_dI hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hb y v (Metric.mem_closedBall_self zero_le_one))
  rw [(hasFDerivAt_int hρ hh hg v).fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [dI_apply]
  exact integral_add (integrable_itg hρ (mom_dh hh z) g v) (integrable_itg hρ hh _ v)
end GlobalTheory.RealWeil.Superpos
