-- Prove2me | solution 1 for GlobalTheory.SocleDet.det_mul_sub_adjugate_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:00.151434+00:00
-- url     : https://prove2.me/submissions/ae5db8b5-292e-47b2-b66d-837ce3e136af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SocleDet
theorem _root_.solution (I : Ideal R) (M : Matrix n n R) (x : n → R) (i l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.det * x l - M.adjugate l i * (M *ᵥ x) i ∈ I := by
  have h1 : (M.adjugate *ᵥ (M *ᵥ x)) l = M.det * x l := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    simp
  have h2 : (M.adjugate *ᵥ (M *ᵥ x)) l = ∑ r, M.adjugate l r * (M *ᵥ x) r := rfl
  rw [← h1, h2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
  exact I.sum_mem fun r hr => I.mul_mem_left _ (h r (Finset.ne_of_mem_erase hr))
end GlobalTheory.SocleDet
