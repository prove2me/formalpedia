-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_res_coindOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:46.95884+00:00
-- url     : https://prove2.me/submissions/8534e2c0-bb0f-4b74-b25e-e3e1868607c1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Theorems.Thm_GroundTheory_GroupCoh_isZero_coindOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory groupCohomology Rep
universe u
variable (k G : Type u) [CommRing k] [Group G] (X : Type u) [AddCommGroup X] [Module k X]
variable {G} (S : Subgroup G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) :
    Limits.IsZero (groupCohomology (res S.subtype (coindOne k G X)) (n + 1)) :=
  (isZero_coindOne k S (G ⧸ S → X) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (resCoindOneIso k X S))
end GroundTheory.GroupCoh
