-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.dI_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:32.335806+00:00
-- url     : https://prove2.me/submissions/4e6bab1a-1238-44f5-83b1-cd25a82b80c9

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
theorem _root_.solution (h : Y → ℂ) (g : V → B) (v : V) (y : Y) (z : V) :
    dI om ρ ι h g v y z = itg om ρ ι (dh om ι h z) g v y + itg om ρ ι h (fun w => fderiv ℝ g w z) v y := by
  simp only [dI, itg, dh, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul, smul_smul]
  rw [add_comm]
  congr 2
  ring
end GlobalTheory.RealWeil.Superpos
