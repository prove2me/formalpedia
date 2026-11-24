-- Prove2me | solution 1 for GlobalTheory.PMon.kronecker_transpose_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:51:01.724314+00:00
-- url     : https://prove2.me/submissions/e527d27c-a968-4a8f-9c4f-8e7803242e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.PMon
theorem _root_.solution {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring
end GlobalTheory.PMon
