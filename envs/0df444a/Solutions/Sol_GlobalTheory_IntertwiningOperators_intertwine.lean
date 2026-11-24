-- Prove2me | solution 1 for GlobalTheory.IntertwiningOperators.intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:11.696145+00:00
-- url     : https://prove2.me/submissions/6444d22a-cde5-492f-ae47-40f29a745de2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwiningOperators
open Polynomial
namespace GlobalTheory.IntertwiningOperators
theorem _root_.solution {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
end GlobalTheory.IntertwiningOperators
