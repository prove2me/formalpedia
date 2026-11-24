-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.map_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:34.751666+00:00
-- url     : https://prove2.me/submissions/b5415f57-f669-40dd-8914-b0a9bde2cc5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution (P Q : Matrix n n K) (Ψ : Matrix n n K[X]) (k : ℕ) :
    ((P.map C * Ψ * Q.map C).map fun p => p.coeff k) = P * (Ψ.map fun p => p.coeff k) * Q := by
  ext i j
  simp only [map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Finset.sum_mul]
end GlobalTheory.CofactorOrder
