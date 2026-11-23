-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:37.251917+00:00
-- url     : https://prove2.me/submissions/7416037b-b559-44a0-9f0f-3602f7dcb14a

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
theorem _root_.solution {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ}
    (hl : l ∈ L.lattice) : (fun z ↦ f (z + l)) = f :=
  funext fun z ↦ hf z l hl
end IsPeriodic
end GroundTheory.Global.Elliptic
