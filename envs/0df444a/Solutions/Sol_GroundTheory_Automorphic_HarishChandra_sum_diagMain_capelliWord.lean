-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.sum_diagMain_capelliWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:23.946825+00:00
-- url     : https://prove2.me/submissions/b3ba5833-a255-46fa-bdcb-7117f7334664

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagMain_capelliWord

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
theorem _root_.solution (k : ℕ) :
    ∑ i : Fin (k + 1) → Fin n,
      diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
        psum (Fin n) ℂ (k + 1) := by
  classical
  simp_rw [diagMain_capelliWord]
  rw [Finset.sum_comm, psum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => c), if_pos (Finset.mem_univ _)]
end GroundTheory.Automorphic.HarishChandra
