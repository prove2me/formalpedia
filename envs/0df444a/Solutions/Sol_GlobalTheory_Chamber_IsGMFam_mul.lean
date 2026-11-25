-- Prove2me | solution 1 for GlobalTheory.Chamber.IsGMFam.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:13.715805+00:00
-- url     : https://prove2.me/submissions/cf6510f7-f764-4021-8e6e-cde863a9b924

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
namespace IsGMFam
theorem _root_.solution {𝔞 : Submodule ℝ (A0 k)} {c d : Finset (SV k) → A0 k → ℂ} (h : IsGMFam 𝔞 c) (h' : IsGMFam 𝔞 d) :
    IsGMFam 𝔞 (c * d) := fun P hP =>
  ⟨(h P hP).1.mul (h' P hP).1, fun Q e l => congrArg₂ (· * ·) ((h P hP).2 Q e l) ((h' P hP).2 Q e l)⟩
end IsGMFam
end GlobalTheory.Chamber
