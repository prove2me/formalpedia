-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:00.555384+00:00
-- url     : https://prove2.me/submissions/c23dce85-92f2-4c19-850c-82086fb5d1c3

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
theorem _root_.solution [Finite N] (χ : QZDual N) (a : N) :
    addCharEquiv χ a = QZ.toComplex (χ a) :=
  rfl
end GroundTheory.ProfCoh.QZDual
