-- Prove2me | solution 1 for GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:08.246356+00:00
-- url     : https://prove2.me/submissions/66c0e7ad-6196-4564-a2ee-e345750a1834

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeAevalLeOfDegLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SZShift
namespace GlobalTheory.SZShift
theorem _root_.solution {σ τ F E : Type} [CommRing F] [CommRing E] [Algebra F E]
    (g : σ → MvPolynomial τ E) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))
end GlobalTheory.SZShift
