-- Prove2me | solution 1 for MazurProof.N13GeneralizedMumfordIntegral.ker_mumfordEval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:47:42.402241+00:00
-- url     : https://prove2.me/submissions/4108537d-6911-4ae9-bb64-a0dc7d41b135

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose

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
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
@[simp] theorem mumfordEval_ySubClass
    (D : SemiMumford (R := R)) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]
theorem mumfordIdeal_le_ker
    (D : SemiMumford (R := R)) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D
theorem ker_mumfordEval
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : R[X] := coeff0 z
    let q : R[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

theorem solution : type_of% @MazurProof.N13GeneralizedMumfordIntegral.ker_mumfordEval := @MazurProof.N13GeneralizedMumfordIntegral.ker_mumfordEval
