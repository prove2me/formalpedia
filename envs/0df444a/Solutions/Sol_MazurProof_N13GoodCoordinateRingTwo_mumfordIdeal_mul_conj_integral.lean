-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal_mul_conj_integral
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:36:24.594431+00:00
-- url     : https://prove2.me/submissions/234024fc-5f38-4fb8-852d-4f12651a48af

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation

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
/-- The characteristic-two generalized graph ideal satisfies
`(u,Y-v)(u,Y+h+v)=(u)`. -/
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford) :
    mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span ({xClass D.u} : Set CoordinateRing) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := D.bezout
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add, xClass_mul]
      have htwoPoly : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      have htwoCoord : (2 : CoordinateRing) = 0 := by
        calc
          (2 : CoordinateRing) = xClass (2 : K[X]) :=
            (xClass_natCast 2).symm
          _ = xClass 0 := by rw [htwoPoly]
          _ = 0 := xClass_zero
      rw [htwoPoly, xClass_zero, zero_mul, zero_add]
      have hvadd : xClass D.v + xClass D.v = 0 := by
        rw [← two_mul, htwoCoord, zero_mul]
      calc
        xClass D.u * xClass hPoly =
            xClass D.u * xClass hPoly +
              xClass D.u * (xClass D.v + xClass D.v) := by
          rw [hvadd, mul_zero, add_zero]
        _ = xClass D.u *
              (yClass - (-xClass hPoly - xClass D.v)) -
            (yClass - xClass D.v) * xClass D.u := by ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal_mul_conj_integral := @MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal_mul_conj_integral
