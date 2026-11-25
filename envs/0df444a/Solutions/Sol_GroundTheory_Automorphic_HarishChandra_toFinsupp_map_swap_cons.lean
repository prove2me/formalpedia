-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.toFinsupp_map_swap_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:25.757527+00:00
-- url     : https://prove2.me/submissions/094c8ce6-1092-4c26-9b9b-649e991eb560

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp (((a :: w).map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      Finsupp.single (a.2, a.1) 1 +
        Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) := by
  rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]
  rfl
end GroundTheory.Automorphic.HarishChandra
