-- Prove2me | solution 1 for GlobalTheory.mem_range_algebraMap_iff_heightOneOrd_vw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:05.736811+00:00
-- url     : https://prove2.me/submissions/d74917b5-bdd3-44f2-b203-4d340c32f793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_forall_height_eq_one

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
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1), 0 ≤ heightOneOrd_vw p hp x := by
  rw [mem_range_algebraMap_iff_forall_height_eq_one]
  exact forall_congr' fun p => forall_congr' fun _ => forall_congr' fun hp =>
    mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx
end GlobalTheory
