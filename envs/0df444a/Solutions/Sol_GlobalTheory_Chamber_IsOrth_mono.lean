-- Prove2me | solution 1 for GlobalTheory.Chamber.IsOrth.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:21.218192+00:00
-- url     : https://prove2.me/submissions/cfb3a10f-26a8-452e-ba75-85267fc5d764

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
theorem _root_.solution {𝔞 𝔟 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) (e : 𝔟 ≤ 𝔞) : IsOrth 𝔟 X :=
  fun P hP => h P (mem_parF.2 ⟨(mem_parF.1 hP).1, (mem_parF.1 hP).2.1.trans e, empty_subset _⟩)
end IsOrth
end GlobalTheory.Chamber
