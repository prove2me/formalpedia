-- Prove2me | solution 1 for GlobalTheory.EigenvalueNormBound.pow_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:42.829607+00:00
-- url     : https://prove2.me/submissions/56538e3d-e61e-4f6f-bb9a-a36e9867ecbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormEigenvalueLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EigenvalueNormBound
namespace GlobalTheory.EigenvalueNormBound
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (μ : ℂ)
    (h : Matrix.mulVec M v = μ • v) (k : ℕ) : Matrix.mulVec (M ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
end GlobalTheory.EigenvalueNormBound
