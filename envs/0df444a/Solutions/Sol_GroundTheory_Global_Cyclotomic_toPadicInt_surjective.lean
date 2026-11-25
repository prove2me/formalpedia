-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.toPadicInt_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:15.541074+00:00
-- url     : https://prove2.me/submissions/5d8c0b89-44e7-4d97-89f1-00d5af763f77

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (q : Nat.Primes) : Function.Surjective (toPadicInt q) := fun z =>
  ⟨ofPadics (Pi.single q z), by
    rw [← toPadics_apply, toPadics_ofPadics, Pi.single_eq_same]⟩
end GroundTheory.Global.Cyclotomic
