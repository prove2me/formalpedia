-- Prove2me | solution 1 for GroundTheory.Global.card_stabilizer_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:05.216865+00:00
-- url     : https://prove2.me/submissions/1c54585c-2e0e-44c4-89fb-5366165a23d3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation

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
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
namespace GroundTheory.Global
theorem _root_.solution {x y : X} (h : y ∈ orbit G x) :
    Nat.card (stabilizer G y) = Nat.card (stabilizer G x) := by
  obtain ⟨g, rfl⟩ := h
  exact (Nat.card_congr (stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm
end GroundTheory.Global
