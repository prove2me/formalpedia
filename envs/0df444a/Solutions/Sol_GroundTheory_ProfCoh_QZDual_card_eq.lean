-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZDual.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:25.981663+00:00
-- url     : https://prove2.me/submissions/2b63a2d9-25e3-4515-85a7-11869f1e8ee8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZDual
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
namespace GroundTheory.ProfCoh.QZDual
theorem _root_.solution [Finite N] : Nat.card (QZDual N) = Nat.card N :=
  (Nat.card_congr (toAddMonoidHomEquiv (A := N)).toEquiv).trans QZ.card_hom
end GroundTheory.ProfCoh.QZDual
