-- Prove2me | solution 1 for GroundTheory.PAdicHodge.smodEq_span_singleton_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.746155+00:00
-- url     : https://prove2.me/submissions/2e4f361a-9ac4-46e6-a42d-53392106c37b

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
variable {R : Type*} [CommRing R]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (a x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GroundTheory.PAdicHodge
