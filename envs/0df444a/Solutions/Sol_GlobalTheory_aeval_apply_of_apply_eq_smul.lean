-- Prove2me | solution 1 for GlobalTheory.aeval_apply_of_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:08.428476+00:00
-- url     : https://prove2.me/submissions/31813691-c623-4a17-883b-88e06dbd4ba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type 1} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (μ : ℂ) (y : V)
    (hy : T y = μ • y) (q : ℂ[X]) : aeval T q y = q.eval μ • y := by
  induction q using Polynomial.induction_on with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n c ih =>
    have e1 : (C c * X ^ (n + 1) : ℂ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, map_mul, Module.End.mul_apply, aeval_X, hy, map_smul, ih]
    conv_rhs => rw [eval_mul, eval_X]
    rw [smul_smul, mul_comm]
end GlobalTheory
