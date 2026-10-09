-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.isDouble_of_finiteIdealSquareRoot
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:41:44.710961+00:00
-- url     : https://prove2.me/submissions/abddbdaa-d863-4796-8d12-4e616fb681fd

import Mathlib
import Definitions.Def_MazurN13_L3
import Theorems.Thm_MazurProof_N13BranchLeading_branch_min_order

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
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

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring
end
end MazurProof.N13BranchNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFactorization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFactorization =====
section
/-!
# Gaussian factorization of the N13 sextic

The N13 sextic is the norm of a cubic over the Gaussian rationals.  This is
the structural input for a Gaussian two-descent.
-/
open Polynomial
namespace MazurProof.N13GaussianFactorization
noncomputable section
/-- The N13 sextic is the sum of the two displayed squares. -/
theorem f_eq_sum_squares : N13Mumford.f ℚ = A ^ 2 + B ^ 2 := by
  simp only [N13Mumford.f, A, B]
  ring
end
end MazurProof.N13GaussianFactorization
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityHalf =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityHalf =====
section
/-!
# A half of the infinity-difference class on the N13 sextic

The Gaussian factorization `f = A² + B²` supplies a balanced Mumford pair
`u = X(X+1)`, `v = -(2X+1)` and the function `g = Y-A`.  We prove

`(u, Y-v)² = (g)` and `ord_{∞₊}(g) = -1`.

The corresponding oriented Picard identity says that this Mumford class
doubles to the difference of the two points at infinity.  This removes the
extra even-degree ambiguity in the fake 2-Kummer kernel.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13InfinityHalf
noncomputable section
open SexticMumford
theorem linearFunction_mul (p q r s : ℚ[X]) :
    N13BranchNorm.linearFunction ℚ p q *
        N13BranchNorm.linearFunction ℚ r s =
      N13BranchNorm.linearFunction ℚ
        (p * r + q * s * N13Mumford.f ℚ)
        (p * s + q * r) := by
  simp only [N13BranchNorm.linearFunction]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M r + xClass M s * yClass M) =
        xClass M p * xClass M r +
          (xClass M p * xClass M s +
            xClass M q * xClass M r) * yClass M +
          xClass M q * xClass M s * yClass M ^ 2 := by ring
    _ = xClass M p * xClass M r +
          (xClass M p * xClass M s +
            xClass M q * xClass M r) * yClass M +
          xClass M q * xClass M s * xClass M (N13Mumford.f ℚ) := by
            rw [show yClass M ^ 2 =
              xClass M (N13Mumford.f ℚ) by
                simpa [M] using yClass_sq M]
    _ = _ := by
      change
        xClass M p * xClass M r +
              (xClass M p * xClass M s +
                xClass M q * xClass M r) * yClass M +
              xClass M q * xClass M s *
                xClass M (N13Mumford.f ℚ) =
          xClass M (p * r + q * s * N13Mumford.f ℚ) +
            xClass M (p * s + q * r) * yClass M
      simp only [xClass_add, xClass_mul]
      ring
theorem four_mul_quarter :
    (4 : ℚ[X]) * C ((4 : ℚ)⁻¹) = 1 := by
  calc
    (4 : ℚ[X]) * C ((4 : ℚ)⁻¹) =
        C (4 : ℚ) * C ((4 : ℚ)⁻¹) := by rw [Polynomial.C_ofNat]
    _ = C ((4 : ℚ) * (4 : ℚ)⁻¹) := by rw [C_mul]
    _ = 1 := by norm_num
theorem two_mul_half :
    (2 : ℚ[X]) * C ((2 : ℚ)⁻¹) = 1 := by
  calc
    (2 : ℚ[X]) * C ((2 : ℚ)⁻¹) =
        C (2 : ℚ) * C ((2 : ℚ)⁻¹) := by rw [Polynomial.C_ofNat]
    _ = C ((2 : ℚ) * (2 : ℚ)⁻¹) := by rw [C_mul]
    _ = 1 := by norm_num
theorem halfFunction_mul_halfA2Factor :
    halfFunction * halfA2Factor = xClass M (halfU ^ 2) := by
  rw [halfFunction, halfA2Factor, linearFunction_mul]
  rw [N13GaussianFactorization.f_eq_sum_squares]
  have h0 :
      (-N13GaussianFactorization.A) *
            (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) +
          1 * C ((4 : ℚ)⁻¹) *
            (N13GaussianFactorization.A ^ 2 +
              N13GaussianFactorization.B ^ 2) =
        halfU ^ 2 := by
    simp [N13GaussianFactorization.B, halfU]
    linear_combination
      (X ^ 2 + 2 * X ^ 3 + X ^ 4) * four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) * C ((4 : ℚ)⁻¹) +
          1 * (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) = 0 := by ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction]
theorem halfFunction_mul_halfABFactor :
    halfFunction * halfABFactor =
      xClass M halfU * ySubClass M halfV := by
  rw [halfFunction, halfABFactor, linearFunction_mul]
  have h0 :
      (-N13GaussianFactorization.A) *
            (halfU + N13GaussianFactorization.A *
              (C ((4 : ℚ)⁻¹) * (X + 1))) +
          1 * (C ((4 : ℚ)⁻¹) * (X + 1)) * N13Mumford.f ℚ =
        halfU * (-halfV) := by
    simp [N13GaussianFactorization.A, N13Mumford.f, halfU, halfV]
    linear_combination
      (X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) *
        four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) *
          (C ((4 : ℚ)⁻¹) * (X + 1)) +
          1 * (halfU +
            N13GaussianFactorization.A *
              (C ((4 : ℚ)⁻¹) * (X + 1))) =
        halfU := by
    ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring
theorem halfFunction_mul_halfB2Factor :
    halfFunction * halfB2Factor =
      ySubClass M halfV * ySubClass M halfV := by
  rw [halfFunction, halfB2Factor, linearFunction_mul]
  have h0 :
      (-N13GaussianFactorization.A) *
            (-2 * halfV +
              N13GaussianFactorization.A * halfB2Q) +
          1 * halfB2Q * N13Mumford.f ℚ =
        N13Mumford.f ℚ + halfV ^ 2 := by
    simp [N13GaussianFactorization.A, N13Mumford.f, halfV, halfB2Q]
    linear_combination
      (5 * X ^ 2 + 12 * X ^ 3 + 10 * X ^ 4 +
        4 * X ^ 5 + X ^ 6) * four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) * halfB2Q +
          1 * (-2 * halfV +
            N13GaussianFactorization.A * halfB2Q) =
        -2 * halfV := by ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction, ySubClass]
  rw [show xClass M (N13Mumford.f ℚ) = yClass M ^ 2 by
    simpa [M] using (yClass_sq M).symm]
  have hc2 : xClass M (2 : ℚ[X]) = 2 := by
    change xClassHom M (2 : ℚ[X]) = 2
    exact map_ofNat (xClassHom M) 2
  rw [hc2]
  ring
theorem halfFunction_back_combination :
    halfFunction =
      xClass M backP * (xClass M halfU * xClass M halfU) +
      xClass M backQ *
        (xClass M halfU * ySubClass M halfV) +
      xClass M backR *
        (ySubClass M halfV * ySubClass M halfV) := by
  simp only [halfFunction, N13BranchNorm.linearFunction, ySubClass]
  calc
    xClass M (-N13GaussianFactorization.A) +
        xClass M 1 * yClass M =
      xClass M
          (backP * halfU ^ 2 +
            backQ * (-halfU * halfV) +
            backR * (N13Mumford.f ℚ + halfV ^ 2)) +
        xClass M
          (backQ * halfU + backR * (-2 * halfV)) *
          yClass M := by
      have h0 :
          backP * halfU ^ 2 +
              backQ * (-halfU * halfV) +
              backR * (N13Mumford.f ℚ + halfV ^ 2) =
            -N13GaussianFactorization.A := by
        simp [N13GaussianFactorization.A, N13Mumford.f, halfU, halfV,
          backP, backQ, backR]
        linear_combination
          (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3 -
            2 * X ^ 4 - 6 * X ^ 5 - 4 * X ^ 6 - X ^ 7) *
              two_mul_half
      have h1 :
          backQ * halfU + backR * (-2 * halfV) = 1 := by
        simp [halfU, halfV, backQ, backR]
        linear_combination (2 * X + 1) * two_mul_half
      rw [h0, h1]
    _ = _ := by
      simp only [xClass_add, xClass_mul, xClass_pow, xClass_neg]
      rw [show xClass M (N13Mumford.f ℚ) = yClass M ^ 2 by
        simpa [M] using (yClass_sq M).symm]
      have hc2 : xClass M (2 : ℚ[X]) = 2 := by
        change xClassHom M (2 : ℚ[X]) = 2
        exact map_ofNat (xClassHom M) 2
      rw [hc2]
      ring
theorem halfFunction_mem_ideal_sq :
    halfFunction ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV := by
  let a := xClass M halfU
  let b := ySubClass M halfV
  have ha : a ∈ mumfordIdeal M halfU halfV :=
    xClass_mem_mumfordIdeal M halfU halfV
  have hb : b ∈ mumfordIdeal M halfU halfV :=
    ySubClass_mem_mumfordIdeal M halfU halfV
  have haa : a * a ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul ha ha
  have hab : a * b ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul ha hb
  have hbb : b * b ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul hb hb
  have hsum :
      xClass M backP * (a * a) + xClass M backQ * (a * b) +
          xClass M backR * (b * b) ∈
        mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ haa)
      (Ideal.mul_mem_left _ _ hab))
      (Ideal.mul_mem_left _ _ hbb)
  rw [halfFunction_back_combination]
  exact hsum
theorem ideal_sq_le_halfFunction :
    mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV ≤
      Ideal.span ({halfFunction} :
        Set (N13Mumford.CoordinateRing ℚ)) := by
  let I := mumfordIdeal M halfU halfV
  let G := Ideal.span ({halfFunction} :
    Set (N13Mumford.CoordinateRing ℚ))
  let a := xClass M halfU
  let b := ySubClass M halfV
  have ha2 : a * a ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfA2Factor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfA2Factor]
    simp [a, pow_two]
  have hab : a * b ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfABFactor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfABFactor]
    simp [a, b, mul_comm]
  have hb2 : b * b ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfB2Factor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfB2Factor]
  apply Ideal.mul_le.mpr
  intro p hp q hq
  obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
  have h00 : (p₀ * q₀) * (a * a) ∈ G :=
    Ideal.mul_mem_left G _ ha2
  have h01 : (p₀ * qY) * (a * b) ∈ G :=
    Ideal.mul_mem_left G _ hab
  have h10 : (pY * q₀) * (a * b) ∈ G :=
    Ideal.mul_mem_left G _ hab
  have h11 : (pY * qY) * (b * b) ∈ G :=
    Ideal.mul_mem_left G _ hb2
  have hsum := Ideal.add_mem G
    (Ideal.add_mem G (Ideal.add_mem G h00 h01) h10) h11
  rw [← hpEq, ← hqEq]
  convert hsum using 1
  all_goals ring
theorem halfIdeal_sq :
    mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV =
      Ideal.span ({halfFunction} :
        Set (N13Mumford.CoordinateRing ℚ)) := by
  apply le_antisymm
  · exact ideal_sq_le_halfFunction
  · rw [Ideal.span_le]
    intro z hz
    simpa only [Set.mem_singleton_iff] using
      hz ▸ halfFunction_mem_ideal_sq
theorem wSeries_coeff_zero :
    (N13Infinity.wSeries ℚ).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ ℚ
    (N13Infinity.sqrtReverseF ℚ)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]
theorem evalPoly_negA_coeff_neg_three :
    (N13BranchNorm.evalPoly ℚ
      (-N13GaussianFactorization.A)).coeff (-3 : ℤ) = -1 := by
  simp [N13BranchNorm.evalPoly, N13GaussianFactorization.A,
    N13Infinity.parameter]
  change ((2 : LaurentSeries ℚ) *
    HahnSeries.single (-2 : ℤ) 1).coeff (-3 : ℤ) = 0
  rw [show (2 : LaurentSeries ℚ) =
    HahnSeries.single (0 : ℤ) 2 by
      rfl]
  rw [HahnSeries.coeff_single_mul]
  norm_num [HahnSeries.coeff_single]
theorem ySeries_coeff_neg_three :
    (N13Infinity.ySeries ℚ).coeff (-3 : ℤ) = 1 := by
  simp only [N13Infinity.ySeries, N13Infinity.parameter,
    HahnSeries.inv_single, inv_one,
    HahnSeries.single_pow, one_pow]
  rw [HahnSeries.coeff_single_mul]
  norm_num
  exact wSeries_coeff_zero
theorem half_normNumerator :
    N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1 = -4 * halfU ^ 2 := by
  simp [N13BranchNorm.normNumerator,
    N13GaussianFactorization.f_eq_sum_squares,
    N13GaussianFactorization.B, halfU]
  ring
theorem half_normNumerator_ne_zero :
    N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1 ≠ 0 := by
  rw [half_normNumerator]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ halfU_monic.ne_zero)
theorem half_normNumerator_natDegree :
    (N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1).natDegree = 4 := by
  rw [half_normNumerator]
  compute_degree! <;>
    simp [halfU_natDegree, halfU_monic.ne_zero]
theorem half_poleDegree :
    N13BranchLeading.poleDegree ℚ
      (-N13GaussianFactorization.A) 1 = 3 := by
  simp [N13BranchLeading.poleDegree, N13GaussianFactorization.A]
  compute_degree!
theorem halfFunction_minus_coeff_neg_three :
    (N13InfinityMinus.coordinateToLaurentMinus ℚ
      halfFunction).coeff (-3 : ℤ) = -2 := by
  rw [show halfFunction =
    N13BranchNorm.linearFunction ℚ
      (-N13GaussianFactorization.A) 1 by rfl,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  simp only [map_one, one_mul, HahnSeries.coeff_sub,
    evalPoly_negA_coeff_neg_three, ySeries_coeff_neg_three]
  norm_num
theorem halfFunction_minus_order :
    (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
      -3 := by
  have hmin := N13BranchLeading.branch_min_order ℚ
    (-N13GaussianFactorization.A) 1 halfFunction_ne_zero
  change min
      (N13Infinity.coordinateToLaurent ℚ halfFunction).order
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
    -(N13BranchLeading.poleDegree ℚ
      (-N13GaussianFactorization.A) 1 : ℤ) at hmin
  rw [half_poleDegree] at hmin
  have hlower : (-3 : ℤ) ≤
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order := by
    omega
  have hupper :
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order ≤
        (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [halfFunction_minus_coeff_neg_three]
      norm_num)
  exact le_antisymm hupper hlower
theorem halfFunction_plus_order :
    (N13Infinity.coordinateToLaurent ℚ halfFunction).order = -1 := by
  have hsum := N13BranchNorm.branch_orders_add ℚ
    (-N13GaussianFactorization.A) 1 half_normNumerator_ne_zero
  rw [half_normNumerator_natDegree] at hsum
  change
    (N13Infinity.coordinateToLaurent ℚ halfFunction).order +
        (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
      -(4 : ℤ) at hsum
  rw [halfFunction_minus_order] at hsum
  omega
theorem ordPlus_halfFunctionUnit :
    (N13Infinity.positiveInfinityOrder ℚ).ordPlus halfFunctionUnit =
      Multiplicative.ofAdd (-1 : ℤ) := by
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent ℚ
        (algebraMap (N13Mumford.CoordinateRing ℚ)
          (N13Mumford.FunctionField ℚ) halfFunction)).order) =
    Multiplicative.ofAdd (-1 : ℤ)
  rw [N13Infinity.functionFieldToLaurent_algebraMap]
  exact congrArg Multiplicative.ofAdd halfFunction_plus_order
theorem halfIdealUnit_sq :
    mumfordIdealUnit M infinityHalf.toSemi ^ 2 =
      toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) halfFunctionUnit := by
  apply Units.ext
  change
    ((mumfordIdealUnit M infinityHalf.toSemi :
        (FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ))ˣ) :
      FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
        (N13Mumford.FunctionField ℚ)) ^
      2 =
    ((toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) halfFunctionUnit :
          (FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
            (N13Mumford.FunctionField ℚ))ˣ) :
        FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ))
  rw [coe_mumfordIdealUnit, coe_toPrincipalIdeal]
  change
    (mumfordIdeal M halfU halfV :
      FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
        (N13Mumford.FunctionField ℚ)) ^ 2 =
      FractionalIdeal.spanSingleton
        (N13Mumford.CoordinateRing ℚ)⁰
        (algebraMap (N13Mumford.CoordinateRing ℚ)
          (N13Mumford.FunctionField ℚ) halfFunction)
  rw [pow_two, ← FractionalIdeal.coeIdeal_mul, halfIdeal_sq,
    FractionalIdeal.coeIdeal_span_singleton]
theorem mumfordRaw_infinityHalf_sq :
    mumfordRaw M infinityHalf * mumfordRaw M infinityHalf =
      principalOriented M (N13Infinity.positiveInfinityOrder ℚ)
          halfFunctionUnit *
        mumfordRaw M (infinityMinusMumford M) := by
  apply Prod.ext
  · change
      mumfordIdealUnit M infinityHalf.toSemi *
          mumfordIdealUnit M infinityHalf.toSemi =
        toPrincipalIdeal
            (N13Mumford.CoordinateRing ℚ)
            (N13Mumford.FunctionField ℚ) halfFunctionUnit *
          mumfordIdealUnit M (infinityMinusMumford M).toSemi
    rw [← pow_two, halfIdealUnit_sq]
    have hinf :
        mumfordIdealUnit M (infinityMinusMumford M).toSemi = 1 := by
      change mumfordIdealUnit M (zero M).toSemi = 1
      exact mumfordIdealUnit_zero M
    rw [hinf, mul_one]
  · change
      Multiplicative.ofAdd ((infinityHalf.nInf : ℤ) - 1) *
          Multiplicative.ofAdd ((infinityHalf.nInf : ℤ) - 1) =
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus halfFunctionUnit *
          Multiplicative.ofAdd
            (((infinityMinusMumford M).nInf : ℤ) - 1)
    rw [ordPlus_halfFunctionUnit]
    norm_num [infinityHalf, infinityMinusMumford]
theorem two_nsmul_classOf_infinityHalf :
    2 • classOf M (N13Infinity.positiveInfinityOrder ℚ) infinityHalf =
      classOf M (N13Infinity.positiveInfinityOrder ℚ)
        (infinityMinusMumford M) := by
  rw [two_nsmul]
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) +
      Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) =
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M)))
  change
    Additive.ofMul
      (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf) *
        QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) =
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M)))
  rw [← map_mul, mumfordRaw_infinityHalf_sq, map_mul]
  have hprincipal :
      QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ) halfFunctionUnit) =
        1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_range.mpr ⟨halfFunctionUnit, rfl⟩)
  rw [hprincipal]
  exact congrArg
    (fun z :
      OrientedFrac M ⧸
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range =>
      Additive.ofMul z)
    (one_mul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M))))
end
end MazurProof.N13InfinityHalf
end

end

-- ===== FLT.Assumptions.MazurProof.N13KummerKernelAssembly =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13KummerKernelAssembly =====
section
/-!
# Removing the even-sextic infinity ambiguity from the N13 Kummer kernel

The generic fake-Kummer kernel theorem for an even sextic has two branches:
a class is either a double, or a double plus the difference of the two
points at infinity.  For N13 the latter class is itself a double, by the
explicit half-class constructed in `N13InfinityHalf`.

This file records the exact group-theoretic assembly.  Its only remaining
input is the genuine generic Kummer-kernel theorem; no finiteness or
representative enumeration occurs here.
-/
namespace MazurProof.N13KummerKernelAssembly
noncomputable section
theorem two_nsmul_infinityHalfClass :
    2 • infinityHalfClass = infinityClass := by
  exact N13InfinityHalf.two_nsmul_classOf_infinityHalf
end
end MazurProof.N13KummerKernelAssembly
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
/-! ## Unfolding the full-gauge fibre -/
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-! ## Closing the finite ideal square -/
namespace FinitePadeGraphRootData
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
theorem mumfordIdealUnit_infinityMinus_eq_one :
    mumfordIdealUnit M
        (infinityMinusMumford M).toSemi = 1 := by
  apply Units.ext
  change
    (mumfordIdeal M 1 0 :
      FractionalIdeal
        (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl
@[simp] theorem pureInfinityClass_neg_one :
    pureInfinityClass (-1) =
      N13KummerKernelAssembly.infinityClass := by
  have hraw :
      mumfordRaw M (infinityMinusMumford M) =
        ((1, Multiplicative.ofAdd (-1)) :
          OrientedFrac M) := by
    apply Prod.ext
    · exact mumfordIdealUnit_infinityMinus_eq_one
    · rfl
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          (mumfordRaw M (infinityMinusMumford M)))
  rw [hraw]
/-- Every pure integer infinity class is an integral multiple of the
difference of the two infinity points. -/
theorem pureInfinityClass_eq_zsmul_infinityClass
    (z : ℤ) :
    pureInfinityClass z =
      (-z) • N13KummerKernelAssembly.infinityClass := by
  rw [← pureInfinityClass_neg_one]
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd z) :
            OrientedFrac M)) =
      Additive.ofMul
        ((QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) ^ (-z))
  apply congrArg Additive.ofMul
  have hraw :
      ((1, Multiplicative.ofAdd z) :
          OrientedFrac M) =
        ((1, Multiplicative.ofAdd (-1)) :
          OrientedFrac M) ^ (-z) := by
    apply Prod.ext
    · simp
    · apply Multiplicative.toAdd.injective
      simp
  calc
    QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd z) :
            OrientedFrac M) =
        QuotientGroup.mk'
          (principalOriented M O).range
          (((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M) ^ (-z)) := by
              rw [hraw]
    _ =
        (QuotientGroup.mk'
          (principalOriented M O).range
          ((1, Multiplicative.ofAdd (-1)) :
            OrientedFrac M)) ^ (-z) := by
              exact
                map_zpow
                  (QuotientGroup.mk'
                    (principalOriented M O).range)
                  ((1, Multiplicative.ofAdd (-1)) :
                    OrientedFrac M) (-z)
/-- A finite fractional-ideal square is sufficient for N13.  Whatever
integer remains at infinity is a multiple of `infinityClass`, and the
already constructed N13 half of that class absorbs it. -/
theorem isDouble_of_finiteIdealSquareRoot
    (D : LowRep)
    (hfinite :
      ∃ I : InvFrac M,
        ∃ α : (FunctionField M)ˣ,
          mumfordIdealUnit M D.toSemi *
              toPrincipalIdeal
                (CoordinateRing M) (FunctionField M) α =
            I ^ 2) :
    ∃ Q : G,
      N13LowDegreeKummerHom.lowClass D = 2 • Q := by
  obtain ⟨I, α, hIdeal⟩ := hfinite
  let H : Subgroup (OrientedFrac M) :=
    (principalOriented M O).range
  let e : ℤ :=
    D.toSemi.nInf - 1 +
      Multiplicative.toAdd (O.ordPlus α)
  let R₀ : OrientedFrac M :=
    (I, Multiplicative.ofAdd 0)
  have hraw :
      semiMumfordRaw M D.toSemi *
          principalOriented M O α =
        R₀ ^ 2 *
          ((1, Multiplicative.ofAdd e) :
            OrientedFrac M) := by
    apply Prod.ext
    · change
        mumfordIdealUnit M D.toSemi *
            toPrincipalIdeal
              (CoordinateRing M) (FunctionField M) α =
          I ^ 2 * 1
      rw [hIdeal, mul_one]
    · change
        Multiplicative.ofAdd (D.toSemi.nInf - 1) *
            O.ordPlus α =
          (Multiplicative.ofAdd 0) ^ 2 *
            Multiplicative.ofAdd e
      apply Multiplicative.toAdd.injective
      change
        D.toSemi.nInf - 1 +
            Multiplicative.toAdd (O.ordPlus α) =
          0 * 2 + e
      simp only [zero_mul, zero_add]
      rfl
  have hprincipal :
      QuotientGroup.mk' H
          (principalOriented M O α) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_range.mpr ⟨α, rfl⟩)
  have hquot :
      QuotientGroup.mk' H
          (semiMumfordRaw M D.toSemi) =
        (QuotientGroup.mk' H R₀) ^ 2 *
          QuotientGroup.mk' H
            ((1, Multiplicative.ofAdd e) :
              OrientedFrac M) := by
    calc
      QuotientGroup.mk' H
            (semiMumfordRaw M D.toSemi) =
          QuotientGroup.mk' H
              (semiMumfordRaw M D.toSemi) * 1 := by
                exact
                  (mul_one
                    (QuotientGroup.mk' H
                      (semiMumfordRaw M D.toSemi))).symm
      _ =
          QuotientGroup.mk' H
              (semiMumfordRaw M D.toSemi) *
            QuotientGroup.mk' H
              (principalOriented M O α) := by
                rw [hprincipal]
      _ =
          QuotientGroup.mk' H
            (semiMumfordRaw M D.toSemi *
              principalOriented M O α) := by
                rw [map_mul]
      _ =
          QuotientGroup.mk' H
            (R₀ ^ 2 *
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M)) := by
                  rw [hraw]
      _ =
          (QuotientGroup.mk' H R₀) ^ 2 *
            QuotientGroup.mk' H
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M) := by
                rw [map_mul, map_pow]
  let Q₀ : G :=
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range R₀)
  dsimp only [H] at hquot
  have hclass :
      N13LowDegreeKummerHom.lowClass D =
        2 • Q₀ + pureInfinityClass e := by
    change
      Additive.ofMul
          (QuotientGroup.mk'
            (principalOriented M O).range
            (semiMumfordRaw M D.toSemi)) =
        2 •
            Additive.ofMul
              (QuotientGroup.mk'
                (principalOriented M O).range R₀) +
          Additive.ofMul
            (QuotientGroup.mk'
              (principalOriented M O).range
              ((1, Multiplicative.ofAdd e) :
                OrientedFrac M))
    simpa only [ofMul_mul,
      ofMul_pow, two_nsmul] using
        congrArg Additive.ofMul hquot
  refine
    ⟨Q₀ +
      (-e) • N13KummerKernelAssembly.infinityHalfClass, ?_⟩
  rw [hclass,
    pureInfinityClass_eq_zsmul_infinityClass,
    ← N13KummerKernelAssembly.two_nsmul_infinityHalfClass]
  simp only [two_nsmul, zsmul_add]
  abel
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.isDouble_of_finiteIdealSquareRoot := @MazurProof.N13MumfordFullKummerIdentityFiber.isDouble_of_finiteIdealSquareRoot
