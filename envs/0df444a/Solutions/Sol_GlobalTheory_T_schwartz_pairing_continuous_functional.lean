-- Prove2me | solution 1 for GlobalTheory.T.schwartz_pairing_continuous_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:09.658118+00:00
-- url     : https://prove2.me/submissions/beb702ed-7283-4d22-82a3-5ef73534be33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzPairingContinuousFunctional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzPairingContinuousFunctionalStatement
import Theorems.Thm_GlobalTheory_schwartz_pairing_conj_clm_of_borelSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ),
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ, L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | exact GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | (intros; apply GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace <;> assumption)
end _root_.GlobalTheory.T
