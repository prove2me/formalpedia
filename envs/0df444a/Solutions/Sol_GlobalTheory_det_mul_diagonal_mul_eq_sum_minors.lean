-- Prove2me | solution 1 for GlobalTheory.det_mul_diagonal_mul_eq_sum_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:39.871389+00:00
-- url     : https://prove2.me/submissions/36814eed-57f8-40c9-9d85-09c59303ab1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_range_subsetEnum
import Theorems.Thm_GlobalTheory_subsetEnum_injective
import Theorems.Thm_GlobalTheory_det_mul_eq_sum_minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring
end GlobalTheory
