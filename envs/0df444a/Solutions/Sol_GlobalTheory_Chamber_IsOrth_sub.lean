-- Prove2me | solution 1 for GlobalTheory.Chamber.IsOrth.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:56.83303+00:00
-- url     : https://prove2.me/submissions/0f931cf1-fcdb-4faf-baac-adc0e1a0754b

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
theorem _root_.solution {𝔞 : Submodule ℝ (A0 k)} {X Y : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) (h' : IsOrth 𝔞 Y) :
    IsOrth 𝔞 (X - Y) := fun P hP Q e => by rw [Pi.sub_apply, Pi.sub_apply, map_sub, ← h P hP Q e, ← h' P hP Q e]
end IsOrth
end GlobalTheory.Chamber
