-- Prove2me | solution 1 for GlobalTheory.CentralIdemIntegral.isIntegral_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:31.37079+00:00
-- url     : https://prove2.me/submissions/9a907c26-b8d8-4da0-986d-b9b4126c345a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
import Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_trace_of_algClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CentralIdemIntegral
namespace GlobalTheory.CentralIdemIntegral
theorem _root_.solution {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical

  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have h := isIntegral_trace_of_algClosed (A.map φ) hn (by rw [← Matrix.map_pow, hA])
  rw [← AddMonoidHom.map_trace] at h
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h
end GlobalTheory.CentralIdemIntegral
