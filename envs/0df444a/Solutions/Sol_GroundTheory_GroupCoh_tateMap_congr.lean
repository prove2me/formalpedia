-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateMap_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:12.239568+00:00
-- url     : https://prove2.me/submissions/5526046e-9ade-491d-9497-78a36bfdf810

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable {X Y Z : Rep k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution {φ ψ : X ⟶ Y} (h : φ = ψ) (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map φ).f i).hom x = ((tateComplex.map ψ).f i).hom x := by
  rw [h]
end GroundTheory.GroupCoh
