-- Prove2me | solution 1 for GlobalTheory.TraceDetSplit.trace_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:21.399602+00:00
-- url     : https://prove2.me/submissions/792d4762-1718-4b88-9e9d-27aa317c8a50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis

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
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
end GlobalTheory.TraceDetSplit
