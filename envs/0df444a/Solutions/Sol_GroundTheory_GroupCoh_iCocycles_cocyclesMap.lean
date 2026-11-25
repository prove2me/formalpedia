-- Prove2me | solution 1 for GroundTheory.GroupCoh.iCocycles_cocyclesMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:28.604126+00:00
-- url     : https://prove2.me/submissions/bc89c0d7-5fd4-4deb-9c06-b15b254985ec

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct

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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    iCocycles A' n (cocyclesMap (MonoidHom.id G) φ n z) =
      fun x => φ.hom (iCocycles A n z x) := by
  change (cocyclesMap (MonoidHom.id G) φ n ≫ iCocycles A' n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl
end GroundTheory.GroupCoh
