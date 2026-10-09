-- Prove2me | solution 1 for MazurProof.N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:49:18.269557+00:00
-- url     : https://prove2.me/submissions/d999e48a-4fe7-488b-88e1-c6c442d3cb65

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
import Theorems.Thm_MazurProof_N13SpecialQuotientBasis_specialData_u_natDegree
import Theorems.Thm_MazurProof_SexticMumford_ker_mumfordEval
import Theorems.Thm_MazurProof_SexticMumford_mumford_root_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
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
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem mumfordEval_yClass (D : SemiMumford M) :
    mumfordEval M D (yClass M) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation M D)
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisor
noncomputable section
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT
/-- Literal equality with the selected special graph ideal already recovers
the monic quadratic and the graph value modulo it.  This is the converse
representative statement to `mumfordIdeal_eq_special_of_graphDivisor_eq`. -/
theorem u_eq_base_and_dvd_v_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  have hxmem :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        mumfordIdeal D.u D.v := by
    rw [hideal]
    exact
      xClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hxker :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hxmem
  have hxzero :=
    RingHom.mem_ker.mp hxker
  rw [mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hxzero
  have hueq :
      D.u = (X ^ 2 + X : K[X]) := by
    have hspecial :
        N13SpecialQuotientBasis.specialData.u = D.u :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        D.u_monic
        N13SpecialQuotientBasis.specialData.u_monic
        hxzero
        (by
          rw [hdeg,
            N13SpecialQuotientBasis.specialData_u_natDegree])
    simpa only [N13SpecialQuotientBasis.specialData_u] using hspecial.symm
  have hymem :
      yClass ∈ mumfordIdeal D.u D.v := by
    rw [hideal]
    change
      yClass ∈
        mumfordIdeal
          N13SpecialQuotientBasis.specialData.u
          N13SpecialQuotientBasis.specialData.v
    simpa only [N13SpecialQuotientBasis.specialData_v,
      ySubClass, xClass_zero, sub_zero] using
      ySubClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hyker :
      yClass ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hymem
  have hyzero :=
    RingHom.mem_ker.mp hyker
  rw [mumfordEval_yClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hyzero
  exact ⟨hueq, hyzero⟩
/-- The literal special graph ideal determines the selected effective
divisor.  The proof recovers the two roots and evaluates the graph there;
it does not enumerate the special curve. -/
theorem graphDivisor_eq_special_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_mumfordIdeal_eq D hdeg hideal
  have hr0 : D.u.IsRoot 0 := by
    simp [hu]
  have hr1 : D.u.IsRoot 1 := by
    change D.u.eval 1 = 0
    rw [hu]
    norm_num
    exact CharP.cast_eq_zero K 2
  have hmem0 :
      (0 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 0).2 hr0
  have hmem1 :
      (1 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 1).2 hr1
  obtain ⟨q, hq⟩ := hv
  have hv0 : D.v.eval 0 = 0 := by
    rw [hq, eval_mul, hr0, zero_mul]
  have hv1 : D.v.eval 1 = 0 := by
    rw [hq, eval_mul, hr1, zero_mul]
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨0, hmem0, ?_⟩
    simp [rootPoint, N13AbelChartBase.p00,
      N13AbelFiberTwoModel.curvePointEquiv, hv0]
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨1, hmem1, ?_⟩
    simp [rootPoint, N13AbelChartBase.p10,
      N13AbelFiberTwoModel.curvePointEquiv, hv1]
  have hpne :
      N13AbelChartBase.p00 ≠ N13AbelChartBase.p10 := by
    intro h
    have h' :=
      congrArg N13AbelFiberTwoModel.curvePointEquiv h
    simp [N13AbelChartBase.p00,
      N13AbelChartBase.p10] at h'
  simpa [N13AbelChartBase.specialBaseDivisor] using
    (Sym2.mem_and_mem_iff hpne).mp ⟨hp00, hp10⟩
end
end MazurProof.N13SpecialGraphDivisor
end

end

theorem solution : type_of% @MazurProof.N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq := @MazurProof.N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq
