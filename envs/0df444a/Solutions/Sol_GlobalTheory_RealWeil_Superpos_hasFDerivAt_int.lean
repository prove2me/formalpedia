-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.hasFDerivAt_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:15.209585+00:00
-- url     : https://prove2.me/submissions/aeebf851-e6f7-403f-9346-331737f1232b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_continuous_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_integrable_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_hasFDerivAt_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_continuous_dI
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_exists_bound

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
    (hg : ContDiff ℝ ∞ g) (v₀ : V) :
    HasFDerivAt (fun v => ∫ y, itg om ρ ι h g v y ∂ν) (∫ y, dI om ρ ι h g v₀ y ∂ν) v₀ := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall fun v => (continuous_itg hρ hh.1 g v).aestronglyMeasurable)
    (integrable_itg hρ hh g v₀) (continuous_dI hρ hh.1 g v₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y v hv => hb y v hv) hbd
    (Filter.Eventually.of_forall fun y v _ => hasFDerivAt_itg (hg.differentiable (by simp)) h v y)
end GlobalTheory.RealWeil.Superpos
