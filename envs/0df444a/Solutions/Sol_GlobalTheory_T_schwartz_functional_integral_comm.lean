-- Prove2me | solution 1 for GlobalTheory.T.schwartz_functional_integral_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:40.103072+00:00
-- url     : https://prove2.me/submissions/dfc40ac8-88ed-4f1a-af72-cbe9e5e6f7b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralCommStatement
import Theorems.Thm_GlobalTheory_SchwartzIntegral_clm_integral_interchange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ) (G : W → Sch (Fin n))
    (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  first | exact @GlobalTheory.SchwartzIntegral.clm_integral_interchange | exact GlobalTheory.SchwartzIntegral.clm_integral_interchange | (intros; apply GlobalTheory.SchwartzIntegral.clm_integral_interchange <;> assumption)
end _root_.GlobalTheory.T
