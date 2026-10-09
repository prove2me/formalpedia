-- Prove2me | solution 1 for MazurProof.SexticMumford.mumfordIdeal_mul_conj_integral
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:49:54.888296+00:00
-- url     : https://prove2.me/submissions/c1fc5e66-61da-4a1a-b150-b1795ccdfa36

import Mathlib
import Definitions.Def_MazurN13_L1
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_mumfordIdeal_mul_conj_integral

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

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
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
namespace Model
end Model
variable (M : Model K)
/-! ## The affine coordinate ring -/
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
/-! ## Balanced triples -/
/-! ## Curve points and their balanced representatives -/
/-! ## Mumford ideals -/
/-! ## The oriented fractional-ideal quotient -/
end
end MazurProof.SexticMumford
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
/-! ## Hyperelliptic conjugation and the quadratic norm -/
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordUnit =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordUnit =====
section
/-!
# Explicit invertibility of Mumford ideals on a smooth sextic

For a semi-Mumford pair `(u,v)`, squarefreeness of the sextic gives
`(u, 2v, (f-v²)/u) = 1`.  Consequently `(u,Y-v) (u,Y+v) = (u)`,
which packages the Mumford ideal as a unit fractional ideal.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem mumford_bezout (D : SemiMumford M) :
    ∃ w a b c : K[X],
      M.f - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : C (2 : K) = (2 : K[X]) := by
          exact map_natCast (C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr M.two_ne_zero)
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ M.f - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ M.f := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        M.ne_zero).mp M.squarefree z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford M) :
    mumfordIdeal M D.u D.v * mumfordIdeal M D.u (-D.v) =
      Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M D.u D.v
  let J := mumfordIdeal M D.u (-D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨p₀ * q₀ * xClass M D.u +
        p₀ * qY * ySubClass M (-D.v) +
        pY * q₀ * ySubClass M D.v +
        pY * qY * xClass M w, ?_⟩
    rw [← hpEq, ← hqEq]
    simp only [ySubClass, xClass_neg, sub_neg_eq_add] at hpEq hqEq ⊢
    have hgraph :
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
          xClass M D.u * xClass M w := by
      calc
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
            yClass M ^ 2 - xClass M D.v ^ 2 := by ring
        _ = xClass M M.f - xClass M (D.v ^ 2) := by
          rw [yClass_sq, xClass_pow]
        _ = xClass M (M.f - D.v ^ 2) := by rw [xClass_sub]
        _ = xClass M (D.u * w) := by rw [hw]
        _ = xClass M D.u * xClass M w := by rw [xClass_mul]
    linear_combination pY * qY * hgraph
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨w, a, b, c, hw, hbez⟩ := mumford_bezout M D
    have huI : xClass M D.u ∈ I :=
      xClass_mem_mumfordIdeal M D.u D.v
    have huJ : xClass M D.u ∈ J :=
      xClass_mem_mumfordIdeal M D.u (-D.v)
    have hvI : ySubClass M D.v ∈ I :=
      ySubClass_mem_mumfordIdeal M D.u D.v
    have hvJ : ySubClass M (-D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal M D.u (-D.v)
    have hu2 : xClass M D.u * xClass M D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass M D.u * xClass M (2 * D.v) ∈ I * J := by
      have hp : xClass M D.u * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm : ySubClass M D.v * xClass M D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add, xClass_mul]
      change xClass M D.u * (2 * xClass M D.v) =
        xClass M D.u * (yClass M + xClass M D.v) -
          (yClass M - xClass M D.v) * xClass M D.u
      ring
    have huw : xClass M D.u * xClass M w ∈ I * J := by
      have hg : ySubClass M D.v * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      convert hg using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add]
      calc
        xClass M D.u * xClass M w = xClass M (D.u * w) := by
          rw [xClass_mul]
        _ = xClass M (M.f - D.v ^ 2) := by rw [hw]
        _ = xClass M M.f - xClass M (D.v ^ 2) := by rw [xClass_sub]
        _ = yClass M ^ 2 - xClass M D.v ^ 2 := by
          rw [yClass_sq, xClass_pow]
        _ = (yClass M - xClass M D.v) *
            (yClass M + xClass M D.v) := by ring
    have ha : xClass M a * (xClass M D.u * xClass M D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M a) hu2
    have hb : xClass M b *
        (xClass M D.u * xClass M (2 * D.v)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M b) huv
    have hc : xClass M c * (xClass M D.u * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M c) huw
    have hsum := Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M D.u * xClass M D.u) +
            xClass M b * (xClass M D.u * xClass M (2 * D.v)) +
            xClass M c * (xClass M D.u * xClass M w) =
          xClass M D.u := by
      calc
        _ = xClass M D.u *
            xClass M (a * D.u + b * (2 * D.v) + c * w) := by
              simp only [xClass_add, xClass_mul]
              ring
        _ = xClass M D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass M D.u := mul_one _
    rw [heq] at hsum
    exact hsum
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.mumfordIdeal_mul_conj_integral := @MazurProof.SexticMumford.mumfordIdeal_mul_conj_integral
