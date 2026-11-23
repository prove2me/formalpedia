-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:47.065783+00:00
-- url     : https://prove2.me/submissions/cc89155b-4c9b-47f8-9764-9bc0c2e5234c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation k G V) (σ : G) :
    cycHerbrand ρ σ = (Nat.card (CycTateZero ρ σ) : ℚ) / Nat.card (CycTateNegOne ρ σ) :=
  rfl
end GroundTheory.Global
