-- Prove2me | solution 1 for GlobalTheory.spanEquivariant_aeval_map_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:52.479983+00:00
-- url     : https://prove2.me/submissions/92f60c65-7635-4c8f-896e-bc999bcb8d3a

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] {V : Type 1} [AddCommGroup V] [Module ℂ V]
    (P : E →+ V) (b : E) (T : Module.End ℂ V) (hT : ∀ x, T (P x) = P (b * x)) (q : ℚ[X]) :
    ∀ x, aeval T (q.map (algebraMap ℚ ℂ)) (P x) = P (aeval b q * x) := by
  induction q using Polynomial.induction_on with
  | C c =>
    intro x
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply]
    have h := map_ratCast_smul P E ℂ c x
    rw [smul_eq_mul] at h
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), h]
  | add p q hp hq =>
    intro x
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, add_mul]
  | monomial n c ih =>
    intro x
    have e1 : (C c * X ^ (n + 1) : ℚ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, Polynomial.map_mul, map_mul, Module.End.mul_apply, Polynomial.map_X, aeval_X, hT, ih,
      show aeval b (C c * X ^ n * X) = aeval b (C c * X ^ n) * b by rw [map_mul, aeval_X], mul_assoc]
end GlobalTheory
