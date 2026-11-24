-- Prove2me | solution 1 for GlobalTheory.TraceDetSplit.det_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:34.420875+00:00
-- url     : https://prove2.me/submissions/834aac0e-246c-43ba-a478-b91c299dd8cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Theorems.Thm_GlobalTheory_TraceDetSplit_det_aeval_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceDetSplit
namespace GlobalTheory.TraceDetSplit
theorem _root_.solution {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]
end GlobalTheory.TraceDetSplit
