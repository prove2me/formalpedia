-- Prove2me | solution 2 for GroundTheory.PAdicHodge.mem_maxUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:56.868836+00:00
-- url     : https://prove2.me/submissions/0a992889-a552-4cd4-ad3a-605322fcf3bc

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
theorem _root_.solution {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {x : PadicAlgCl p} :
    x ∈ maxUnramified p K ↔ x ∈ K ∧ x ∈ unramifiedClosure p :=
  Iff.rfl
end GroundTheory.PAdicHodge
