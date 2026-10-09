-- Prove2me | solution 1 for MazurProof.N13FullNormPairGaussian.norm_gaussianI
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:11:04.656198+00:00
-- url     : https://prove2.me/submissions/26f2d9ee-fcb7-4137-9048-9c9bca1e9f5e

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalArithmetic
noncomputable section
@[simp] theorem i_sq : i ^ 2 = -1 := by
  rfl
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
/-!
# The Gaussian fraction field as a quadratic number field

The fraction field of `ℤ[i]` has the structural rational basis `(1,i)`.
The only localization point to check is that inverting nonzero ordinary
integers already inverts every nonzero Gaussian integer: `z` divides its
nonzero integer norm `z * star z`.

No embeddings or Gaussian elements are enumerated.
-/
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
/-! ## The integral basis `(1,i)` -/
/-! ## Cofinality of ordinary integer denominators -/
/-! ## The localized rational basis -/
/-! ## Power basis, minimal polynomial, and discriminant -/
/-- Localization identifies the field norm on `K/ℚ` with the same Gaussian
norm. -/
theorem fieldNorm_algebraMap (z : GI) :
    Algebra.norm ℚ (algebraMap GI K z) =
      algebraMap ℤ ℚ (Zsqrtd.norm z) := by
  rw [Algebra.norm_localization
    ℤ (nonZeroDivisors ℤ) z,
    algebraNorm_eq_gaussianNorm]
end
end MazurProof.N13GaussianFractionField
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNumberField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNumberField =====
section
/-!
# The absolute N13 number field

The N13 Gaussian cubic is a degree-three extension of the quadratic
Gaussian field.  Combining the structural bases in the two stages gives
the six-element rational basis

`1, α, α², i, iα, iα²`.

This is a tower-basis construction; no embeddings or field elements are
enumerated.
-/
open Algebra Module
namespace MazurProof.N13GaussianNumberField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianNumberField.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNumberField.fieldL
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraL
/- The subtype algebras otherwise prefer transitive `Subalgebra.algebra`
instances.  For a tower starting at `ℤ`, use the unique canonical integer
algebra structures so their modules are definitionally the usual `zsmul`
modules carried by the explicit bases. -/
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraRelativeIntegers
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraAbsoluteIntegers
@[simp] theorem finrank_K_L :
    Module.finrank K L = 3 := by
  rw [Module.finrank_eq_card_basis relativeBasis]
  simp
/-! ## The absolute ring of integers -/
/- Mathlib packages the ring of integers as a separate definition rather
than exposing the integral-closure subtype directly.  This carrier-preserving
equivalence is the explicit bridge between the two presentations. -/
/-! ## Absolute discriminant -/
end
end MazurProof.N13GaussianNumberField
end

end

-- ===== FLT.Assumptions.MazurProof.N13FullNormPairGaussian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FullNormPairGaussian =====
section
/-!
# The N13 full norm-pair sign is gauge-trivial

The N13 sextic field is a cubic extension of the Gaussian field, so it
contains a unit `i` with

`i² = -1`,  `Norm(i) = 1`.

Consequently the square/norm gauge at `i`, multiplied by the scalar/cubic
gauge at `-1`, is exactly the sign pair `(1,-1)`.  Thus the distinguished
sign class in the full norm-pair target is already trivial for N13.

This is a field-structure argument.  It uses neither divisor enumeration
nor a finite square-class certificate.
-/
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLs
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLg
/-- The absolute norm of `i` is one: the relative norm through the cubic
Gaussian extension is `i³ = -i`, whose Gaussian norm is one. -/
theorem norm_gaussianI :
    Algebra.norm ℚ N13GaussianFieldEquiv.gaussianI = 1 := by
  letI : Module.Free ℚ K :=
    Module.Free.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Finite ℚ K :=
    Module.Finite.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Free K Lg :=
    Module.Free.of_basis
      N13GaussianCubicField.powerBasis.basis
  letI : Module.Finite K Lg :=
    Module.Finite.of_basis
      N13GaussianCubicField.powerBasis.basis
  rw [N13GaussianFieldEquiv.gaussianI,
    ← Algebra.norm_norm (R := ℚ) (S := K),
    Algebra.norm_algebraMap,
    N13GaussianNumberField.finrank_K_L]
  have hi3 :
      (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 3 =
        -(algebraMap GI K N13GaussianGlobalArithmetic.i) := by
    calc
      (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 3 =
          (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 2 *
            algebraMap GI K N13GaussianGlobalArithmetic.i := by
              ring
      _ = algebraMap GI K
            (N13GaussianGlobalArithmetic.i ^ 2) *
            algebraMap GI K N13GaussianGlobalArithmetic.i := by
              rw [map_pow]
      _ = -(algebraMap GI K
          N13GaussianGlobalArithmetic.i) := by
              rw [N13GaussianGlobalArithmetic.i_sq,
                map_neg, map_one]
              ring
  rw [hi3, ← map_neg,
    N13GaussianFractionField.fieldNorm_algebraMap]
  norm_num [N13GaussianGlobalArithmetic.i, Zsqrtd.norm]
end
end MazurProof.N13FullNormPairGaussian
end

end

theorem solution : type_of% @MazurProof.N13FullNormPairGaussian.norm_gaussianI := @MazurProof.N13FullNormPairGaussian.norm_gaussianI
