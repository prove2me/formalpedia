-- Prove2me | solution 1 for GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:08.745807+00:00
-- url     : https://prove2.me/submissions/ac5dd611-fa0c-465a-946b-a7f4f5bee77c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartzStatement
import Theorems.Thm_GlobalTheory_integrable_sq_pow_mul_iteratedFDeriv_schwartz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ), Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by
  first | exact @GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz | exact GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz | (intros; apply GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz <;> assumption)
end _root_.GlobalTheory.T
