-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.sum_diagExp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:36.459858+00:00
-- url     : https://prove2.me/submissions/148d5393-f31f-4952-8701-bfcccce1ab4f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) :
    ((diagExp m).sum fun _ e => e) ≤ m.degree := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [diagExp_apply]
  exact Finset.single_le_sum (f := fun j => m (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end GroundTheory.Automorphic.HarishChandra
