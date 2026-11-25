-- Prove2me | solution 1 for GlobalTheory.Chamber.IsOrth.isGMFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:17.59716+00:00
-- url     : https://prove2.me/submissions/7aa64400-23eb-4836-9d40-c07dbd7fb37e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
namespace IsOrth
theorem _root_.solution {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) : IsGMFam 𝔞 (expFam X) :=
  fun P hP => ⟨Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_id.inner ℝ contDiff_const))), fun Q e l => by
      simp only [expFam, eL, h P hP Q e, pr, Submodule.inner_starProjection_left_eq_right]⟩
end IsOrth
end GlobalTheory.Chamber
