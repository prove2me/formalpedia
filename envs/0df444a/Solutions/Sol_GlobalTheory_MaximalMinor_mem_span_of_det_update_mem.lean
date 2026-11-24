-- Prove2me | solution 1 for GlobalTheory.MaximalMinor.mem_span_of_det_update_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:28.170214+00:00
-- url     : https://prove2.me/submissions/c66730c7-a586-47d2-a4c5-848e9d0257d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
import Theorems.Thm_GlobalTheory_MaximalMinor_det_smul_eq_sum_det_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
open GlobalTheory
open GlobalTheory.MaximalMinor
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MaximalMinor
theorem _root_.solution (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by
  choose a ha using fun i => mem_span_singleton.1 (hx i)
  refine (mem_span_range_iff_exists_fun A).2 ⟨a, ?_⟩
  have h1 : b.det v • (∑ i, a i • v i) = b.det v • x := by
    rw [det_smul_eq_sum_det_update b v x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, smul_assoc, ← algebraMap_smul R (a i), ← algebraMap_smul R (a i), smul_comm]
  apply b.equivFun.injective
  ext j
  have h2 := congrArg (fun y => b.equivFun y j) h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hv).1 h2
end GlobalTheory.MaximalMinor
