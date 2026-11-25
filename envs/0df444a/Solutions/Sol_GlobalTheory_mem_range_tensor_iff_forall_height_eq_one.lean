-- Prove2me | solution 1 for GlobalTheory.mem_range_tensor_iff_forall_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:00.532247+00:00
-- url     : https://prove2.me/submissions/4946c948-42a6-48ef-bcb4-f2230fadde9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_iff_forall_height_eq_one_of_projective
import Theorems.Thm_GlobalTheory_mem_range_rTensor_iff

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Projective A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
        v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M) := by
  rw [mem_range_iff_forall_height_eq_one_of_projective]
  exact forall_congr' fun p => forall_congr' fun _ => forall_congr' fun _ =>
    (mem_range_rTensor_iff p (primeLocalSubalgebra K p) v).symm
end GlobalTheory
