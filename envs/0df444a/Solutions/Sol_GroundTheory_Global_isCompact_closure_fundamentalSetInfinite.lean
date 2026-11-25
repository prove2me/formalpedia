-- Prove2me | solution 1 for GroundTheory.Global.isCompact_closure_fundamentalSetInfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:48.174804+00:00
-- url     : https://prove2.me/submissions/502629a3-a594-4a79-888d-792ef3caf82e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice

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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution :
    IsCompact (closure (fundamentalSetInfinite K)) := by
  rw [fundamentalSetInfinite, ← Homeomorph.preimage_closure, Homeomorph.isCompact_preimage]
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
end GroundTheory.Global
