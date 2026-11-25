-- Prove2me | solution 1 for GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:57.370899+00:00
-- url     : https://prove2.me/submissions/7b61e31f-f769-4cf9-b815-ec7302ac5b46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_iff_forall_height_eq_one_of_projective

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
theorem _root_.solution (x : K) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p := by
  simp only [mem_primeLocalSubalgebra_iff]
  exact mem_range_iff_forall_height_eq_one_of_projective (Algebra.linearMap A K) x
end GlobalTheory
