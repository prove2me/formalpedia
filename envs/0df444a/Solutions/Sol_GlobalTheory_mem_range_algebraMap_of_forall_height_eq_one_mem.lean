-- Prove2me | solution 1 for GlobalTheory.mem_range_algebraMap_of_forall_height_eq_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:45.306228+00:00
-- url     : https://prove2.me/submissions/6e763102-d3df-457b-8b49-1850c9f544ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_of_forall_height_eq_one_of_projective

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
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {x : K} {a : A} (ha : a ≠ 0)
    (hax : a • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range :=
  mem_range_of_forall_height_eq_one_of_projective (Algebra.linearMap A K)
    (IsFractionRing.injective A K) ha hax fun p _ hp hap =>
      (mem_primeLocalSubalgebra_iff p x).mp (h p hp hap)
end GlobalTheory
