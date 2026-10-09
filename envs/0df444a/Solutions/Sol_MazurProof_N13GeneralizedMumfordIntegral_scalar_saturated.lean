-- Prove2me | solution 1 for MazurProof.N13GeneralizedMumfordIntegral.scalar_saturated
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:49:21.129091+00:00
-- url     : https://prove2.me/submissions/8572c2c8-dc26-4322-bbf3-13b4f234fa66

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- A generalized Mumford graph ideal is saturated with respect to every
nonzero scalar from a domain base. -/
theorem scalar_saturated
    [IsDomain R]
    (D : SemiMumford (R := R))
    (r : R) (hr : r ≠ 0)
    (z : CoordinateRing (R := R))
    (hz : xClass (C r) * z ∈ mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v := by
  have hker :
      xClass (C r) * z ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval]
    exact hz
  have hmap :
      mumfordEval D (xClass (C r) * z) = 0 :=
    hker
  have hscalar :
      r • mumfordEval D z =
        Ideal.Quotient.mk
          (Ideal.span ({D.u} : Set R[X])) (C r) *
            mumfordEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (mumfordEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))).map_mul (C r) p
  have hsmul : r • mumfordEval D z = 0 := by
    rw [hscalar]
    simpa only [map_mul, mumfordEval_xClass] using hmap
  have heval : mumfordEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  exact heval
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

theorem solution : type_of% @MazurProof.N13GeneralizedMumfordIntegral.scalar_saturated := @MazurProof.N13GeneralizedMumfordIntegral.scalar_saturated
