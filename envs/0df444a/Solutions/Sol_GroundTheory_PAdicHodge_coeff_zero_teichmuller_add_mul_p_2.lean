-- Prove2me | solution 2 for GroundTheory.PAdicHodge.coeff_zero_teichmuller_add_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:50.635556+00:00
-- url     : https://prove2.me/submissions/68ae3a67-c0d4-40ed-9092-a15d22ee5ede

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
    (teichmuller p c + v * p).coeff 0 = c := by
  rw [add_coeff_zero, teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]
end GroundTheory.PAdicHodge
