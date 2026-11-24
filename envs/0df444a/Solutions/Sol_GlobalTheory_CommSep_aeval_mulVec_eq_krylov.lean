-- Prove2me | solution 1 for GlobalTheory.CommSep.aeval_mulVec_eq_krylov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:04.178531+00:00
-- url     : https://prove2.me/submissions/0c642551-f2b5-4090-94a8-991f017b2e15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.CommSep
namespace GlobalTheory.CommSep
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (v c : Fin r → E) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.CommSep
