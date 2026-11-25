-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axExponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:11.918813+00:00
-- url     : https://prove2.me/submissions/06b36586-88e3-4bc1-b55e-5ccd9d42a5ad

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
omit hp
namespace GroundTheory.PAdicHodge
theorem _root_.solution : axExponent p 0 = 0 := by simp [axExponent]
end GroundTheory.PAdicHodge
