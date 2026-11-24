-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.algebraMap_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:12.017544+00:00
-- url     : https://prove2.me/submissions/c17a88a5-3dbe-4f38-a0d0-6da235d388d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
variable {I : Submodule ℂ (RatFunc ℂ)}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (P : ℂ[X]) {R : RatFunc ℂ}
    (hR : R ∈ I) : algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I := by
  suffices h : ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I from h R hR
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · intro R hR
    rw [RatFunc.algebraMap_C, ← RatFunc.smul_eq_C_mul]
    exact I.smul_mem a hR
  · intro R hR
    rw [map_add, add_mul]
    exact I.add_mem (hp R hR) (hq R hR)
  · intro R hR
    have : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ (k + 1)) * R =
        RatFunc.X * (algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ k) * R) := by
      rw [pow_succ, ← mul_assoc, map_mul _ (Polynomial.C a * Polynomial.X ^ k), RatFunc.algebraMap_X]
      ring
    rw [this]
    exact hX _ (h R hR)
end GroundTheory.Automorphic.GodementJacquet
