-- Prove2me | solution 1 for GlobalTheory.T.haar_measure_pi_change_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:21.546884+00:00
-- url     : https://prove2.me/submissions/20823a6d-6746-4ded-b970-c84763b20bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstantStatement
import Theorems.Thm_GlobalTheory_IdealChain_integral_scale_change_haar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  first | exact @GlobalTheory.IdealChain.integral_scale_change_haar | exact GlobalTheory.IdealChain.integral_scale_change_haar | (intros; apply GlobalTheory.IdealChain.integral_scale_change_haar <;> assumption)
end _root_.GlobalTheory.T
