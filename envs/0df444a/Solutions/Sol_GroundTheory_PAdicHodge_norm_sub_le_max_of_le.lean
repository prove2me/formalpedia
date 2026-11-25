-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_le_max_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:05.989392+00:00
-- url     : https://prove2.me/submissions/9bbbb26b-eda4-4316-bca4-499b51ca77e7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x b y : PadicAlgCl p} {s t : ℝ} (h1 : ‖x - b‖ ≤ s)
    (h2 : ‖b - y‖ ≤ t) : ‖x - y‖ ≤ max s t := by
  rw [← sub_add_sub_cancel x b y]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 h2)
end GroundTheory.PAdicHodge
