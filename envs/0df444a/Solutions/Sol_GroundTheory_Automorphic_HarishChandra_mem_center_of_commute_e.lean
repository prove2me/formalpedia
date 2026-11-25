-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_center_of_commute_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:15.989324+00:00
-- url     : https://prove2.me/submissions/8cf4fee5-6d14-4fd1-86ff-613899c81459

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction

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
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {z : U n} (hz : ∀ a, e a * z = z * e a) :
    z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  induction u using U.induction with
  | halg r => exact Algebra.commutes r z
  | hι X =>
    rw [ι_eq_sum_e, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, mul_smul_comm, hz]
  | hmul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]
end GroundTheory.Automorphic.HarishChandra
