-- Prove2me | solution 1 for GlobalTheory.IntertwinerCoprimeCharpoly.aeval_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:39.303947+00:00
-- url     : https://prove2.me/submissions/202d25f2-89a6-448f-add8-38b18e69be83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfIntertwineOfIsCoprimeCharpoly
import Theorems.Thm_GlobalTheory_IntertwinerCoprimeCharpoly_pow_intertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwinerCoprimeCharpoly
open Polynomial
namespace GlobalTheory.IntertwinerCoprimeCharpoly
theorem _root_.solution {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]
end GlobalTheory.IntertwinerCoprimeCharpoly
