-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coeff_zero_teichmuller_add_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:49:45.225611+00:00
-- url     : https://prove2.me/submissions/28c11543-700c-46c9-a516-605638523ac0

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
theorem _root_.solution (c : A) (v : WittVector p A) :
    (teichmuller p c + v * p).coeff 0 = c := by
  first
    | (have h : WittVector.constantCoeff (teichmuller p c + v * (p : WittVector p A)) = c := by
         rw [map_add, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, add_zero]
         exact WittVector.teichmuller_coeff_zero p c
       exact h)
    | (show WittVector.constantCoeff (teichmuller p c + v * (p : WittVector p A)) = c
       rw [map_add, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, add_zero]
       simp [WittVector.constantCoeff_apply])

