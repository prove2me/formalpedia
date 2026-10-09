-- Prove2me | solution 1 for MazurProof.SexticMumford.OrientedBaseChange.nonZeroDivisors_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:50:57.331441+00:00
-- url     : https://prove2.me/submissions/aca847a9-0bb9-45cb-96c9-6b51936d4d59

import Mathlib
import Definitions.Def_MazurN13_L3
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)
@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num
@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp
@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
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
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 M (xClass M p) = p := by
  change (C p %ₘ curvePoly M).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)
@[simp] theorem coeff0_yClass : coeff0 M (yClass M) = 0 := by
  change (X %ₘ curvePoly M).coeff 0 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num
theorem eq_iff_coeff (z w : CoordinateRing M) :
    z = w ↔ coeff0 M z = coeff0 M w ∧ coeffY M z = coeffY M w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose M z, ← recompose M w, h0, hY]
/-! ## Hyperelliptic conjugation and the quadratic norm -/
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
/-!
# Base change of oriented Picard classes for smooth sextics

An injective coefficient map carrying one sextic equation to another induces
maps on the affine coordinate rings, their fraction fields, and invertible
fractional ideals.  If the distinguished infinity orders are compatible,
the resulting map on oriented fractional ideals descends to an additive map
of the concrete oriented Picard groups.

The construction is algebraic: extension of fractional ideals and a quotient
universal property.  It does not use a relative Picard scheme.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_xClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (p : K[X]) :
    coordinateMap ι hM (xClass M p) =
      xClass M' (p.map ι) := by
  exact AdjoinRoot.map_of
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM) p
@[simp] theorem coordinateMap_yClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    coordinateMap ι hM (yClass M) = yClass M' := by
  exact AdjoinRoot.map_root
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM)
@[simp] theorem coeff0_xClass_mul_yClass
    (N : Model K) (p : K[X]) :
    coeff0 N (xClass N p * yClass N) = 0 := by
  rw [show xClass N p =
    algebraMap K[X] (CoordinateRing N) p from rfl]
  rw [← Algebra.smul_def, map_smul, coeff0_yClass, smul_zero]
@[simp] theorem coeffY_xClass_mul_yClass
    (N : Model K) (p : K[X]) :
    coeffY N (xClass N p * yClass N) = p := by
  rw [show xClass N p =
    algebraMap K[X] (CoordinateRing N) p from rfl]
  rw [← Algebra.smul_def, map_smul, coeffY_yClass, smul_eq_mul,
    mul_one]
@[simp] theorem coeff0_coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (z : CoordinateRing M) :
    coeff0 M' (coordinateMap ι hM z) =
      (coeff0 M z).map ι := by
  rw [← recompose M z]
  simp
@[simp] theorem coeffY_coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (z : CoordinateRing M) :
    coeffY M' (coordinateMap ι hM z) =
      (coeffY M z).map ι := by
  rw [← recompose M z]
  simp
/-- An injective coefficient map remains injective on the rank-two affine
coordinate ring. -/
theorem coordinateMap_injective
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    Function.Injective (coordinateMap ι hM) := by
  intro z w h
  apply (eq_iff_coeff M z w).2
  constructor
  · apply Polynomial.map_injective ι hι
    simpa only [coeff0_coordinateMap] using congrArg (coeff0 M') h
  · apply Polynomial.map_injective ι hι
    simpa only [coeffY_coordinateMap] using congrArg (coeffY M') h
/-- A nonzero element of the source coordinate ring stays nonzero after
coefficient extension. -/
theorem nonZeroDivisors_le_comap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    (CoordinateRing M)⁰ ≤
      Submonoid.comap (coordinateMap ι hM) (CoordinateRing M')⁰ := by
  intro z hz
  rw [mem_nonZeroDivisors_iff_ne_zero] at hz
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  simpa using (coordinateMap_injective ι hι hM).ne hz
end
end MazurProof.SexticMumford.OrientedBaseChange
end

end

theorem solution : type_of% @MazurProof.SexticMumford.OrientedBaseChange.nonZeroDivisors_le_comap := @MazurProof.SexticMumford.OrientedBaseChange.nonZeroDivisors_le_comap
