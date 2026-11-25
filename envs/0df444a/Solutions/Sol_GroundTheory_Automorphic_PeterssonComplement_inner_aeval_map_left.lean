-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.inner_aeval_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:46.708536+00:00
-- url     : https://prove2.me/submissions/ecf1324e-868e-4619-90f4-beb5a5f5d10b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}
namespace GroundTheory.Automorphic.PeterssonComplement
theorem _root_.solution {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X]) (x y : V) :
    inner ℂ (ι (aeval T (p.map (algebraMap ℝ ℂ)) x)) (ι y) =
      inner ℂ (ι x) (ι (aeval T (p.map (algebraMap ℝ ℂ)) y)) := by
  have hcomm : ∀ q : ℂ[X], ∀ z, T (aeval T q z) = aeval T q (T z) := by
    intro q z
    have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
    rw [aeval_X] at h
    exact congrArg (fun L : Module.End ℂ V => L z) h.eq
  revert x y
  induction p using Polynomial.induction_on with
  | C a =>
    intro x y
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply, map_smul, inner_smul_left,
      inner_smul_right, Complex.coe_algebraMap, Complex.conj_ofReal]
  | add p q hp hq =>
    intro x y
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right, hp, hq]
  | monomial k a ih =>
    intro x y
    have e : ((C a * X ^ (k + 1) : ℝ[X]).map (algebraMap ℝ ℂ)) =
        (C a * X ^ k : ℝ[X]).map (algebraMap ℝ ℂ) * X := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X]
    rw [e, map_mul, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih (T x) y, hT, hcomm]
end GroundTheory.Automorphic.PeterssonComplement
