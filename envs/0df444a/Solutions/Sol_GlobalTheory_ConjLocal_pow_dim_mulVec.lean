-- Prove2me | solution 1 for GlobalTheory.ConjLocal.pow_dim_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:24.953983+00:00
-- url     : https://prove2.me/submissions/09705f82-e40b-4543-ac1b-cb281ff4cf18

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.ConjLocal
theorem _root_.solution [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl
end GlobalTheory.ConjLocal
