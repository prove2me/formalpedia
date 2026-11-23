-- Prove2me | solution 1 for GlobalTheory.exists_orbit_eq_primesOver_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:37.249992+00:00
-- url     : https://prove2.me/submissions/7a50b89b-16fe-4db8-8c49-4648274e48c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (P : Ideal B) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := Ideal.nonempty_primesOver (S := A) P
  exact ⟨Q, hQ, hQP, Algebra.IsInvariant.orbit_eq_primesOver B A G P Q⟩
end GlobalTheory
