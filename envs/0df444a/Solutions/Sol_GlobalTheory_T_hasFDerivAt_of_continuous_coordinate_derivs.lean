-- Prove2me | solution 1 for GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:31.497024+00:00
-- url     : https://prove2.me/submissions/673b6146-31ac-47a1-b6da-0a674abe56fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartialsStatement
import Theorems.Thm_GlobalTheory_hasFDerivAt_of_continuous_partials


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
theorem _root_.solution : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_partials | exact GlobalTheory.hasFDerivAt_of_continuous_partials | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_partials <;> assumption)
end _root_.GlobalTheory.T
