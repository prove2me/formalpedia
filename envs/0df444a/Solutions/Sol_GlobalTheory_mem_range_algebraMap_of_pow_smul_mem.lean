-- Prove2me | solution 1 for GlobalTheory.mem_range_algebraMap_of_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:53.455948+00:00
-- url     : https://prove2.me/submissions/71484b67-2d6f-4c6e-b026-df2d41d4cd04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_of_forall_height_eq_one_mem

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
theorem _root_.solution {x : K} {a : A} (ha : a ≠ 0) {n : ℕ}
    (hax : a ^ n • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range :=
  mem_range_algebraMap_of_forall_height_eq_one_mem (pow_ne_zero n ha) hax
    fun p hp h1 hap => h p h1 (hp.mem_of_pow_mem n hap)
end GlobalTheory
