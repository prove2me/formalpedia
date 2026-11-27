-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.iff_perfectRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:56.851691+00:00
-- url     : https://prove2.me/submissions/e6160d17-a03c-41ae-a9ca-f8f8ed2ebe4e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_perfectRing
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_perfectRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP K p] [CompleteSpace K]
    (h : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1) :
    IsPerfectoidField K p ↔ PerfectRing K p :=
  ⟨fun _ => perfectRing p, fun _ => of_perfectRing p h⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
