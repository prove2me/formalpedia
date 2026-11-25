-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:04.174971+00:00
-- url     : https://prove2.me/submissions/1a875d93-ccf5-43b8-8d98-8166d21851eb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure

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
theorem _root_.solution {x : PadicAlgCl p} {m : ℕ} (hm : 0 < m)
    (hc : m.Coprime p) (hx : x ^ m = 1) : x ∈ unramifiedClosure p :=
  IntermediateField.subset_adjoin _ _ ⟨m, hm, hc, hx⟩
end GroundTheory.PAdicHodge
