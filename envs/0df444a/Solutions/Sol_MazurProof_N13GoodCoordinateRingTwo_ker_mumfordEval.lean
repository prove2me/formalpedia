-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.ker_mumfordEval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:07.41269+00:00
-- url     : https://prove2.me/submissions/d3bd522b-24ce-4c7a-912e-e27065affc05

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose

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
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
@[simp] theorem mumfordEval_ySubClass (D : SemiMumford) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]
theorem mumfordIdeal_le_ker (D : SemiMumford) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D
/-- The generalized Mumford graph ideal is exactly the evaluation kernel. -/
theorem ker_mumfordEval (D : SemiMumford) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 z
    let q : K[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set K[X]))
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
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.ker_mumfordEval := @MazurProof.N13GoodCoordinateRingTwo.ker_mumfordEval
