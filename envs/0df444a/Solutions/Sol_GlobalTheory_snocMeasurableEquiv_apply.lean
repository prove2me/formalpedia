-- Prove2me | solution 1 for GlobalTheory.snocMeasurableEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:22.742789+00:00
-- url     : https://prove2.me/submissions/b6057dcf-f440-4b72-a7eb-82c7fd081d42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (p : (Fin n → ℂ) × ℂ) :
    snocMeasurableEquiv n p = Fin.snoc (α := fun _ => ℂ) p.1 p.2 := by
  simp [snocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.insertNthEquiv, Fin.insertNth_last']
end GlobalTheory
