-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coeff_one_teichmuller_add_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.881531+00:00
-- url     : https://prove2.me/submissions/3622f136-f331-4299-a73d-ff6d59636e0f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

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
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]
omit [PerfectRing A p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (c : A) (v : WittVector p A) :
    (teichmuller p c + v * p).coeff 1 = v.coeff 0 ^ p := by
  rw [coeff_add_of_disjoint 1 _ _ fun n => ?_, teichmuller_coeff_pos p c 1 one_pos, zero_add,
    mul_charP_coeff_succ]
  rcases n with _ | n
  · exact Or.inr (mul_charP_coeff_zero v)
  · exact Or.inl (teichmuller_coeff_pos p c (n + 1) n.succ_pos)
end GroundTheory.PAdicHodge
