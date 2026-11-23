-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_coindOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:43.874794+00:00
-- url     : https://prove2.me/submissions/7929d21f-5950-4b4f-8af0-6777ff9f9288

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoindOne

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
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) : Limits.IsZero (groupCohomology (coindOne k G X) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton (Rep.trivial k (⊥ : Subgroup G) X) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (coindOneIsoCoind k G X) ≪≫
      groupCohomology.coindIso _ (n + 1))
end GroundTheory.GroupCoh
