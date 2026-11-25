-- Prove2me | solution 2 for GlobalTheory.isIntegral_int_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:30.635251+00:00
-- url     : https://prove2.me/submissions/82104e09-214b-40ca-af96-7dcea4a1401c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComplexMatrixGaussSumNormIntegralGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [h]⟩
end GlobalTheory
