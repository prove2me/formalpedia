-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galCp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:15.251162+00:00
-- url     : https://prove2.me/submissions/410aef87-ad8e-4d67-b5aa-13b10e439ffd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp

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
open UniformSpace Topology Filter
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : galCp σ x = σ • x := rfl
end GroundTheory.PAdicHodge
