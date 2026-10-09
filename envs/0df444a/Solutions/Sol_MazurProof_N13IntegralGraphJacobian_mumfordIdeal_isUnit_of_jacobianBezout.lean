-- Prove2me | solution 1 for MazurProof.N13IntegralGraphJacobian.mumfordIdeal_isUnit_of_jacobianBezout
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:03:52.276503+00:00
-- url     : https://prove2.me/submissions/666ec8df-f3a0-4532-aef0-b2d1531c9d41

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
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
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
/-- The product of the two raw graph functions is the negative substituted
curve equation.  No divisibility or smoothness hypothesis is needed. -/
theorem ySubClass_mul_conjugateV_raw
    (v : R[X]) :
    ySubClass v * ySubClass (conjugateV v) =
      -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
  calc
    ySubClass v * ySubClass (conjugateV v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass v ^ 2 + xClass hPoly * xClass v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (v ^ 2 + hPoly * v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
      rw [xClass_sub]
      ring
/-- The two conjugate graph functions multiply to the negative Cantor
quotient.  This identity is valid integrally, before reduction modulo two. -/
theorem ySubClass_mul_conjugate
    (D : SemiMumford (R := R)) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) :=
      ySubClass_mul_conjugateV_raw D.v
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]
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
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 M (xClass M p) = p := by
  change (C p %ₘ curvePoly M).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)
/-! ## Hyperelliptic conjugation and the quadratic norm -/
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.GraphJacobianDualFrame =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GraphJacobianDualFrame =====
section
/-!
# A Jacobian dual frame for a graph ideal

For a graph ideal `(U,G)`, the factorization

`G * Gbar = -(U * W)`

places `-Gbar/U` in the multiplier inverse.  If two Jacobian rows generate
one, their graph decompositions then give an explicit two-term dual frame.
This proves invertibility without Noetherian, regular-local, divisor-class,
or special-fibre arguments.
-/
open scoped nonZeroDivisors
namespace MazurProof.GraphJacobianDualFrame
noncomputable section
variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
/-- A graph factorization and a global Jacobian Bézout identity produce an
explicit dual frame, hence an invertible graph fractional ideal. -/
theorem graphJacobian_isUnit
    (U G Gbar W Fy Fx Ux Wx Vx hx a b : A)
    (hU : U ≠ 0)
    (hGGbar : G * Gbar = -(U * W))
    (hFy : Fy = G + Gbar)
    (hFx :
      Fx =
        Ux * W + U * Wx - Vx * Gbar +
          (hx + Vx) * G)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    dsimp only [I]
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    intro hmapU0
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hGGbarK :
      algebraMap A K G * algebraMap A K Gbar =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGGbar
  let z : K :=
    -algebraMap A K Gbar / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K Gbar := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K Gbar *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K Gbar) /
            algebraMap A K U := by
              ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by
              rw [hGGbarK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change
      y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * Gbar + d * W, ?_⟩
    calc
      algebraMap A K (-c * Gbar + d * W) =
          algebraMap A K c *
              (-algebraMap A K Gbar) +
            algebraMap A K d *
              algebraMap A K W := by
                simp only [map_add, map_mul, map_neg]
                ring
      _ =
          algebraMap A K c *
              (z * algebraMap A K U) +
            algebraMap A K d *
              (z * algebraMap A K G) := by
                rw [← hzU, ← hzG]
      _ =
          z * algebraMap A K
            (c * U + d * G) := by
              simp only [map_add, map_mul]
              ring
      _ = z * algebraMap A K yA := by
            rw [hcd]
  have hone_inv : (1 : K) ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    simpa only [one_mul] using hI_le_one hy
  have hIntegral (r : A) :
      algebraMap A K r ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hone_inv)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, mul_one] using hr
  have hScalarZ (r : A) :
      algebraMap A K r * z ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hz_mem)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def] using hr
  let tU : K :=
    algebraMap A K a *
        (algebraMap A K Wx +
          algebraMap A K Vx * z) -
      algebraMap A K b * z
  let tG : K :=
    algebraMap A K a *
        (algebraMap A K Ux * z +
          algebraMap A K hx +
          algebraMap A K Vx) +
      algebraMap A K b
  have htU : tU ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Wx +
            algebraMap A K Vx * z ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (hIntegral Wx) (hScalarZ Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
        hscaled (hScalarZ b))
  have htG : tG ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Ux * z +
            algebraMap A K hx +
            algebraMap A K Vx ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem
          (hScalarZ Ux) (hIntegral hx))
        (hIntegral Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        hscaled (hIntegral b))
  have hGbarK :
      algebraMap A K Gbar =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K Ux * algebraMap A K W +
          algebraMap A K U * algebraMap A K Wx -
          algebraMap A K Vx *
            algebraMap A K Gbar +
          (algebraMap A K hx +
              algebraMap A K Vx) *
            algebraMap A K G := by
    simpa only [map_add, map_sub, map_mul] using
      congrArg (algebraMap A K) hFx
  have hFx_decomp :
      algebraMap A K Fx =
        algebraMap A K U *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) +
          algebraMap A K G *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) := by
    calc
      algebraMap A K Fx =
          algebraMap A K Ux *
              algebraMap A K W +
            algebraMap A K U *
              algebraMap A K Wx -
            algebraMap A K Vx *
              algebraMap A K Gbar +
            (algebraMap A K hx +
                algebraMap A K Vx) *
              algebraMap A K G :=
        hFxK
      _ =
          algebraMap A K U *
              (algebraMap A K Wx +
                algebraMap A K Vx * z) +
            algebraMap A K G *
              (algebraMap A K Ux * z +
                algebraMap A K hx +
                algebraMap A K Vx) := by
              rw [hWK, hGbarK]
              ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K G +
          algebraMap A K Gbar := by
    simpa only [map_add] using
      congrArg (algebraMap A K) hFy
  have hFy_decomp :
      algebraMap A K Fy =
        algebraMap A K U * (-z) +
          algebraMap A K G := by
    calc
      algebraMap A K Fy =
          algebraMap A K G +
            algebraMap A K Gbar :=
        hFyK
      _ =
          algebraMap A K U * (-z) +
            algebraMap A K G := by
              rw [hGbarK]
              ring
  have hBezK :
      algebraMap A K a *
            algebraMap A K Fx +
          algebraMap A K b *
            algebraMap A K Fy = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (algebraMap A K) hBez
  have hframe :
      algebraMap A K U * tU +
          algebraMap A K G * tG = 1 := by
    calc
      algebraMap A K U * tU +
            algebraMap A K G * tG =
          algebraMap A K a *
              (algebraMap A K U *
                  (algebraMap A K Wx +
                    algebraMap A K Vx * z) +
                algebraMap A K G *
                  (algebraMap A K Ux * z +
                    algebraMap A K hx +
                    algebraMap A K Vx)) +
            algebraMap A K b *
              (algebraMap A K U * (-z) +
                algebraMap A K G) := by
                dsimp only [tU, tG]
                ring
      _ =
          algebraMap A K a *
              algebraMap A K Fx +
            algebraMap A K b *
              algebraMap A K Fy := by
                rw [← hFx_decomp, ← hFy_decomp]
      _ = 1 := hBezK
  have hmul_le : I * I⁻¹ ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hxy :=
      (FractionalIdeal.mem_inv_iff hI_ne).mp
        hy x hx
    simpa only [mul_comm] using hxy
  have hone_le : 1 ≤ I * I⁻¹ := by
    rw [FractionalIdeal.one_le, ← hframe]
    simpa only [FractionalIdeal.mem_coe] using
      (((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (FractionalIdeal.mul_mem_mul hU_I htU)
          (FractionalIdeal.mul_mem_mul hG_I htG))
  have hmul_eq : I * I⁻¹ = 1 :=
    le_antisymm hmul_le hone_le
  have hunitI : IsUnit I :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      hmul_eq
  simpa only [I, M] using hunitI
end
end MazurProof.GraphJacobianDualFrame
end

end

-- ===== FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore =====
section
/-!
# Graph ideals on a generalized quadratic curve

Let `A` be an algebra generated by a horizontal coordinate map
`R[X] → A` and an ordinate `y` satisfying

`y² + h(x)y = rhs(x)`.

For a polynomial graph `y = v(x)` whose residual curve equation is
`v² + hv - rhs = uw`, the graph ideal and its hyperelliptic conjugate
multiply to the principal ideal `(u)`, provided the displayed generalized
Jacobian admits a Bézout identity.  The proof is purely ring-theoretic and
works over an arbitrary commutative base ring.
-/
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- The product of the two raw graph functions is the negative substituted
curve equation. -/
theorem ySubClass_mul_conjugateV_raw
    (xClass : R[X] →+* A) (yClass : A) (h rhs v : R[X])
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass v *
        ySubClass xClass yClass (conjugateV h v) =
      -xClass (v ^ 2 + h * v - rhs) := by
  calc
    ySubClass xClass yClass v *
          ySubClass xClass yClass (conjugateV h v) =
        yClass ^ 2 + xClass h * yClass -
          (xClass v ^ 2 + xClass h * xClass v) := by
      simp only [ySubClass, conjugateV, map_neg, map_sub]
      ring
    _ = xClass rhs - xClass (v ^ 2 + h * v) := by
      rw [hy, map_add, map_mul, map_pow]
    _ = -xClass (v ^ 2 + h * v - rhs) := by
      rw [map_sub]
      ring
theorem ySubClass_mul_conjugate
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass D.v *
        ySubClass xClass yClass (conjugateV h D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass xClass yClass D.v *
          ySubClass xClass yClass (conjugateV h D.v) =
        -xClass (D.v ^ 2 + h * D.v - rhs) :=
      ySubClass_mul_conjugateV_raw xClass yClass h rhs D.v hy
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [map_mul]
end
end MazurProof.GeneralizedGraphIdealCore
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
/-!
# Integral N13 graph ideals and the affine Jacobian

This file instantiates the generic graph-Jacobian dual frame for the good
integral N13 equation.  A short resultant certificate proves that the two
relative Jacobian rows generate one globally, so every integral Mumford
graph ideal is invertible.  No fixed special graph or point classification
is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralGraphJacobian.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRingDomain
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralFunctionFieldFractionRing
open N13GeneralizedMumfordIntegral
theorem derivative_curve_eq
    (D : SemiMumford₂) :
    (C (2 : R₂) * D.v + hPoly) *
          derivative D.v +
          derivative hPoly * D.v -
        derivative rhsPoly =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h
/-- The `Y`-Jacobian row is the sum of the graph function and its
hyperelliptic conjugate. -/
theorem jacobianY_eq_graph_add_conjugate
    (D : SemiMumford₂) :
    jacobianY =
      ySubClass D.v +
        ySubClass (conjugateV D.v) := by
  simp only [jacobianY, ySubClass, conjugateV,
    xClass_neg, xClass_sub]
  ring
/-- Differentiating the integral Mumford equation decomposes the
`X`-Jacobian row along the two graph generators. -/
theorem jacobianX_eq_graph_decomposition
    (D : SemiMumford₂) :
    jacobianX =
      xClass (derivative D.u) * xClass D.w +
        xClass D.u * xClass (derivative D.w) -
        xClass (derivative D.v) *
          ySubClass (conjugateV D.v) +
        (xClass (derivative hPoly) +
            xClass (derivative D.v)) *
          ySubClass D.v := by
  have h :=
    congrArg
      (xClass (R := R₂))
      (derivative_curve_eq D)
  have htwo :
      xClass (R := R₂) (C (2 : R₂)) =
        (2 : IntegralRing) := by
    rw [show C (2 : R₂) = (2 : R₂[X]) by
      exact map_natCast C 2]
    exact xClass_natCast 2
  simp only [jacobianX, ySubClass, conjugateV,
    xClass_add, xClass_sub, xClass_neg,
    xClass_mul] at h ⊢
  rw [htwo] at h
  linear_combination h
/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/
/-- A global relative-Jacobian Bézout pair makes every integral smooth
Mumford graph invertible by the explicit graph dual frame. -/
theorem mumfordIdeal_isUnit_of_jacobianBezout
    (D : SemiMumford₂)
    (a b : IntegralRing)
    (hBez :
      a * jacobianX + b * jacobianY = 1) :
    IsUnit
      ((mumfordIdeal D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClass D.u)
      (G := ySubClass D.v)
      (Gbar := ySubClass (conjugateV D.v))
      (W := xClass D.w)
      (Fy := jacobianY)
      (Fx := jacobianX)
      (Ux := xClass (derivative D.u))
      (Wx := xClass (derivative D.w))
      (Vx := xClass (derivative D.v))
      (hx := xClass (derivative hPoly))
      (a := a) (b := b)
  · intro hzero
    apply D.u_monic.ne_zero
    have hcoeff :=
      congrArg (coeff0 (R := R₂)) hzero
    simpa only [coeff0_xClass, map_zero] using hcoeff
  · exact ySubClass_mul_conjugate D
  · exact jacobianY_eq_graph_add_conjugate D
  · exact jacobianX_eq_graph_decomposition D
  · exact hBez
end
end MazurProof.N13IntegralGraphJacobian
end

end

theorem solution : type_of% @MazurProof.N13IntegralGraphJacobian.mumfordIdeal_isUnit_of_jacobianBezout := @MazurProof.N13IntegralGraphJacobian.mumfordIdeal_isUnit_of_jacobianBezout
