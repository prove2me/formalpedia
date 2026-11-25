-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.grpK_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:47.543374+00:00
-- url     : https://prove2.me/submissions/f6b79c11-3fbd-4606-908d-c06efd9ad1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
variable {n : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
theorem _root_.solution (k : ℕ) : grpK (fun _ : Fin k => true) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  ext g
  simp [grpK]
end GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
