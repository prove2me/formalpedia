-- Prove2me | solution 1 for GlobalTheory.ColumnSumLemma.colSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:03.167799+00:00
-- url     : https://prove2.me/submissions/f9f54ea9-6d2d-42b7-bf4d-35cddc5350ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ColumnSumLemma
open Matrix
namespace GlobalTheory.ColumnSumLemma
theorem _root_.solution {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
end GlobalTheory.ColumnSumLemma
