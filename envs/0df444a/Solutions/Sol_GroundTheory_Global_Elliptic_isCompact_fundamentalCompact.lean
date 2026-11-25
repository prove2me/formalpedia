-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isCompact_fundamentalCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:19.708304+00:00
-- url     : https://prove2.me/submissions/f03abd82-eaf7-44f0-b6e8-30185fca4974

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
theorem _root_.solution : IsCompact (fundamentalCompact L) :=
  (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
end GroundTheory.Global.Elliptic
