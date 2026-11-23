-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:17.29462+00:00
-- url     : https://prove2.me/submissions/82a19cbe-1064-4d1b-8ff8-d354159693d2

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
namespace GroundTheory.Global.Elliptic
namespace IsPeriodic
theorem _root_.solution {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : f (z - l) = f z := by
  simpa using (hf (z - l) l hl).symm
end IsPeriodic
end GroundTheory.Global.Elliptic
