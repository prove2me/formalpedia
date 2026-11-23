-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_p_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:33.346273+00:00
-- url     : https://prove2.me/submissions/dff8516d-574f-4859-9671-a06b17990684

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_algCl_lt_one

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
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  exact norm_natCast_p_algCl_lt_one
end GroundTheory.PAdicHodge
