-- Prove2me | solution 1 for MazurProof.SexticMumford.IntegralOrientedRep.exists_semiMumford
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:47:06.184058+00:00
-- url     : https://prove2.me/submissions/1da429e0-9a8d-425c-9463-b2200112718e

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_SexticMumford_IntegralOrientedRep_ideal_ne_bot
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
/-! ## Hyperelliptic conjugation and the quadratic norm -/
theorem norm_recompose (p q : K[X]) :
    norm M (xClass M p + xClass M q * yClass M) =
      xClass M (p ^ 2 - q ^ 2 * M.f) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M p + xClass M q * -yClass M) =
        xClass M p ^ 2 - xClass M q ^ 2 * yClass M ^ 2 := by ring
    _ = xClass M p ^ 2 - xClass M q ^ 2 * xClass M M.f := by
      rw [yClass_sq]
    _ = xClass M (p ^ 2 - q ^ 2 * M.f) := by
      change
        AdjoinRoot.of (curvePoly M) p ^ 2 -
            AdjoinRoot.of (curvePoly M) q ^ 2 *
              AdjoinRoot.of (curvePoly M) M.f =
          AdjoinRoot.of (curvePoly M) (p ^ 2 - q ^ 2 * M.f)
      simp only [map_sub, map_mul, map_pow]
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
theorem norm_eq_xClass_coeff (M : Model K) (z : CoordinateRing M) :
    norm M z =
      xClass M
        ((coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f) := by
  conv_lhs =>
    rw [← recompose M z]
  exact norm_recompose M (coeff0 M z) (coeffY M z)
@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
namespace IntegralOrientedRep
end IntegralOrientedRep
/-- A nonzero ideal has nonzero contraction to `K[X]`.  The structural
reason is that the quadratic norm of any nonzero ideal element is a nonzero
polynomial lying in the contraction. -/
theorem idealContraction_ne_bot (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : idealContraction M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let p : K[X] :=
    (coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f
  have hconj : conjugate M z ≠ 0 := by
    intro hc
    apply hz
    calc
      z = conjugate M (conjugate M z) :=
        (conjugate_involutive M z).symm
      _ = 0 := by rw [hc, map_zero]
  have hnorm : norm M z ≠ 0 :=
    mul_ne_zero hz hconj
  have hp : p ≠ 0 := by
    intro hp
    apply hnorm
    rw [norm_eq_xClass_coeff]
    change xClass M p = 0
    rw [hp, xClass_zero]
  intro hbot
  have hpmem : p ∈ idealContraction M J := by
    change xClass M p ∈ J
    rw [← norm_eq_xClass_coeff]
    exact J.mul_mem_right (conjugate M z) hzJ
  rw [hbot, Ideal.mem_bot] at hpmem
  exact hp hpmem
theorem contractionGenerator_monic (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : (contractionGenerator M J).Monic := by
  classical
  unfold contractionGenerator
  apply Polynomial.monic_normalize
  intro hgen
  exact idealContraction_ne_bot M J hJ
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (idealContraction M J)).mpr hgen)
theorem span_contractionGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contractionGenerator M J} : Set K[X]) =
      idealContraction M J := by
  classical
  unfold contractionGenerator
  calc
    Ideal.span
        ({_root_.normalize
          (Submodule.IsPrincipal.generator
            (idealContraction M J))} : Set K[X]) =
        Ideal.span
          ({Submodule.IsPrincipal.generator
            (idealContraction M J)} : Set K[X]) := by
      apply Ideal.span_singleton_eq_span_singleton.mpr
      exact (associated_normalize
        (Submodule.IsPrincipal.generator
          (idealContraction M J))).symm
    _ = idealContraction M J :=
      Ideal.span_singleton_generator (idealContraction M J)
theorem xClass_contractionGenerator_mem
    (J : Ideal (CoordinateRing M)) :
    xClass M (contractionGenerator M J) ∈ J := by
  change contractionGenerator M J ∈ idealContraction M J
  rw [← span_contractionGenerator M J]
  exact Ideal.subset_span (Set.mem_singleton _)
/-- If an integral ideal has contraction `(u)` and contains one graph
generator `Y-v`, then it is exactly the corresponding Mumford ideal.  This
is the quadratic Hermite-normal-form step, proved from the rank-two
coefficient decomposition. -/
theorem mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    (J : Ideal (CoordinateRing M)) (u v : K[X])
    (hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]))
    (hgraph : ySubClass M v ∈ J) :
    mumfordIdeal M u v = J := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change u ∈ idealContraction M J
      rw [hcontraction]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact hgraph
  · intro w hw
    let q : K[X] := coeffY M w
    let r : CoordinateRing M :=
      w - xClass M q * ySubClass M v
    have hrJ : r ∈ J :=
      J.sub_mem hw (J.mul_mem_left (xClass M q) hgraph)
    have hrY : coeffY M r = 0 := by
      simp [r, q]
    have hrRecompose : xClass M (coeff0 M r) = r := by
      simpa [hrY] using recompose M r
    have hrContract :
        coeff0 M r ∈ idealContraction M J := by
      change xClass M (coeff0 M r) ∈ J
      rw [hrRecompose]
      exact hrJ
    rw [hcontraction, Ideal.mem_span_singleton] at hrContract
    obtain ⟨t, ht⟩ := hrContract
    have hrMumford : r ∈ mumfordIdeal M u v := by
      rw [← hrRecompose, ht, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left _ (xClass M t)
        (xClass_mem_mumfordIdeal M u v)
    have hgraphMumford :
        xClass M q * ySubClass M v ∈ mumfordIdeal M u v :=
      Ideal.mul_mem_left _ (xClass M q)
        (Ideal.subset_span (by simp))
    have hwdecomp :
        w = r + xClass M q * ySubClass M v := by
      simp [r]
    rw [hwdecomp]
    exact Ideal.add_mem _ hrMumford hgraphMumford
/-- A primitive nonzero integral ideal has a semireduced Mumford
presentation.  The `u`-polynomial is the canonical contraction generator,
and `v` is reduced modulo `u`.  No degree bound or class enumeration enters
the proof. -/
theorem exists_semiMumford_of_primitive
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥)
    (hprimitive : IdealIsPrimitive M J) (n : ℤ) :
    ∃ D : SemiMumford M,
      mumfordIdeal M D.u D.v = J ∧
      D.u = contractionGenerator M J ∧
      D.nInf = n := by
  obtain ⟨z, hzJ, hzY⟩ := hprimitive
  let u : K[X] := contractionGenerator M J
  let v0 : K[X] := -(coeff0 M z)
  let v : K[X] := v0 % u
  have huMonic : u.Monic :=
    contractionGenerator_monic M J hJ
  have hu : u ≠ 0 := huMonic.ne_zero
  have hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]) :=
    (span_contractionGenerator M J).symm
  have hgraph0 : ySubClass M v0 = z := by
    calc
      ySubClass M v0 =
          xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              simp [ySubClass, v0, hzY]
              ring
      _ = z := recompose M z
  have hvdecomp : v + u * (v0 / u) = v0 :=
    EuclideanDomain.mod_add_div v0 u
  have hgraph : ySubClass M v ∈ J := by
    have hpoly : v0 - v = u * (v0 / u) := by
      calc
        v0 - v = (v + u * (v0 / u)) - v :=
          congrArg (fun t : K[X] => t - v) hvdecomp.symm
        _ = u * (v0 / u) := by ring
    have hmultiple :
        xClass M (v0 - v) ∈ J := by
      rw [hpoly, xClass_mul, mul_comm]
      exact J.mul_mem_left (xClass M (v0 / u))
        (xClass_contractionGenerator_mem M J)
    have heq :
        ySubClass M v =
          ySubClass M v0 + xClass M (v0 - v) := by
      simp [ySubClass, xClass_sub]
    rw [heq]
    exact J.add_mem (hgraph0 ▸ hzJ) hmultiple
  have hcurve : u ∣ M.f - v ^ 2 := by
    have hprod :
        ySubClass M v * (yClass M + xClass M v) =
          xClass M (M.f - v ^ 2) := by
      simp only [ySubClass]
      calc
        (yClass M - xClass M v) *
            (yClass M + xClass M v) =
            yClass M ^ 2 - xClass M v ^ 2 := by ring
        _ = xClass M M.f - xClass M v ^ 2 := by
          rw [yClass_sq]
        _ = xClass M (M.f - v ^ 2) := by
          rw [xClass_sub, xClass_pow]
    have hmem :
        M.f - v ^ 2 ∈ idealContraction M J := by
      change xClass M (M.f - v ^ 2) ∈ J
      rw [← hprod]
      exact J.mul_mem_right (yClass M + xClass M v) hgraph
    rw [hcontraction, Ideal.mem_span_singleton] at hmem
    exact hmem
  let D : SemiMumford M :=
    { u := u
      v := v
      nInf := n
      u_monic := huMonic
      v_reduced := by
        rw [Polynomial.mod_eq_self_iff hu]
        exact EuclideanDomain.mod_lt _ hu
      curve_dvd := hcurve }
  refine ⟨D, ?_, rfl, rfl⟩
  exact mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    M J u v hcontraction hgraph
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction =====
section
/-!
# Structural reduction of oriented sextic ideals

This file joins the two algebraic seams:

* polynomial-content division produces a primitive integral ideal;
* primitive integral ideals have semi-Mumford graph form.

It then packages the well-founded affine-degree step.  Infinity balancing
is deliberately a separate phase.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
theorem IntegralOrientedRep.exists_semiMumford
    (R : IntegralOrientedRep M)
    (hprimitive : IdealIsPrimitive M R.ideal) :
    ∃ D : SemiMumford M,
      semiMumfordClass M O D = R.picClass M O ∧
      mumfordIdeal M D.u D.v = R.ideal := by
  obtain ⟨D, hIdeal, -, hn⟩ :=
    exists_semiMumford_of_primitive M R.ideal
      (R.ideal_ne_bot M) hprimitive (R.atInfinity + 1)
  have hunit : mumfordIdealUnit M D = R.unit := by
    apply Units.ext
    rw [coe_mumfordIdealUnit, hIdeal, ← R.coe_unit]
  have hraw : semiMumfordRaw M D = R.raw M := by
    apply Prod.ext
    · exact hunit
    · change
        Multiplicative.ofAdd (D.nInf - 1) =
          Multiplicative.ofAdd R.atInfinity
      congr 1
      rw [hn]
      omega
  refine ⟨D, ?_, hIdeal⟩
  change
    Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (semiMumfordRaw M D)) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (R.raw M))
  rw [hraw]
/-! ## A canonical affine-degree step -/
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.IntegralOrientedRep.exists_semiMumford := @MazurProof.SexticMumford.IntegralOrientedRep.exists_semiMumford
