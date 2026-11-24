-- Prove2me | solution 1 for GlobalTheory.Chamber.vecSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:42.402532+00:00
-- url     : https://prove2.me/submissions/35261adf-298c-4f00-9e2d-601fcc3c74cf

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
theorem _root_.solution {P Q : Finset (SV k)} (e : Q ⊆ P) : aP Q ≤ aP P := Submodule.span_mono (Set.image_mono e)
end GlobalTheory.Chamber
