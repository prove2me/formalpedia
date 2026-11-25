-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateMap_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:12.918006+00:00
-- url     : https://prove2.me/submissions/975ac046-15c0-46d2-812c-cd7487375a70

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
theorem _root_.solution (φ : X ⟶ Y) (i j : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map φ).f j).hom (((tateComplex X).d i j).hom x) =
      ((tateComplex Y).d i j).hom (((tateComplex.map φ).f i).hom x) := by
  have h := (tateComplex.map φ).comm i j
  exact congr(($h).hom x).symm
end GroundTheory.GroupCoh
