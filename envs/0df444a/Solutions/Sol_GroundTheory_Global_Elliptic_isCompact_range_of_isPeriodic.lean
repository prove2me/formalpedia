-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isCompact_range_of_isPeriodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:20.448836+00:00
-- url     : https://prove2.me/submissions/12516688-c05e-4e22-a706-16fc390fadf4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hc : Continuous f) (hf : IsPeriodic L f) : IsCompact (range f) :=
  IsZLattice.isCompact_range_of_periodic L.lattice f hc fun z w hw ↦ hf z w hw
end GroundTheory.Global.Elliptic
