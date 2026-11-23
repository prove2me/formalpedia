-- Prove2me | solution 1 for GlobalTheory.mem_range_algebraMap_iff_mem_primeLocalSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:03.909324+00:00
-- url     : https://prove2.me/submissions/0b365efb-934f-48d7-a761-70b895abd3e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [p.IsPrime]
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] [Algebra B K]
    [IsScalarTower A B K] (x : K) :
    x ∈ (algebraMap B K).range ↔ x ∈ primeLocalSubalgebra K p := by
  rw [mem_range_algebraMap_atPrime_iff p B, mem_primeLocalSubalgebra_iff]
end GlobalTheory
