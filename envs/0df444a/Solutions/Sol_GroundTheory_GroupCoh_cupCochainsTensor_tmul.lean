-- Prove2me | solution 1 for GroundTheory.GroupCoh.cupCochainsTensor_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:39.725316+00:00
-- url     : https://prove2.me/submissions/dbee3b18-61ca-44de-97dc-bc5477160a62

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupCochainsTensor A B p q (f ⊗ₜ g) = cupCochain rfl f g :=
  rfl
end GroundTheory.GroupCoh
