-- Prove2me | solution 1 for MazurProof.N13ReciprocalInfinityContraction.xbar_mul_tbar
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:18:53.942563+00:00
-- url     : https://prove2.me/submissions/36fddc57-61e2-4e73-bcb4-0222022f3acc

import Mathlib
import Definitions.Def_MazurN13_L4

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

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphSaturation =====
section
/-!
# Vertical saturation of reflected N13 infinity graphs

A monic graph on the integral infinity chart has quotient
`R₂[X] / (u)`, hence its quotient has no torsion from a nonzero base
scalar.  For a monic quadratic `u`, weighted reflection also makes the
affine coordinate `x` a unit modulo the reflected graph ideal.  These two
facts, together with equality on the ordinary overlap, show that the
reflected affine ideal is the canonical vertical contraction of its
generic fibre.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphSaturation.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralInfinityGraphSaturation.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralInfinityGraphSaturation.rationalRingLocalization
/-- A monic polynomial of degree two is determined by its two lower
coefficients. -/
theorem monic_quadratic_eq
    (u : R₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    u = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
  have hc₂ : u.coeff 2 = 1 := by
    calc
      u.coeff 2 = u.coeff u.natDegree :=
        congrArg u.coeff hdeg.symm
      _ = 1 := hu.coeff_natDegree
  have hdegree : u.degree ≤ 2 := by
    rw [degree_eq_natDegree hu.ne_zero, hdeg]
    norm_num
  calc
    u =
        C (u.coeff 2) * X ^ 2 +
          C (u.coeff 1) * X +
          C (u.coeff 0) :=
      u.eq_quadratic_of_degree_le_two hdegree
    _ = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
      rw [hc₂, C_1]
      ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end

end

-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IrreducibleQuadraticChart =====
section
/-!
# The proper chart of an irreducible quadratic N13 graph

An irreducible monic quadratic over `ℚ₂` cannot have one root in each
valuation regime.  A root-free Hensel argument gives the exact Newton
dichotomy: either both ordinary coefficients are integral, or both
coefficients of the reciprocal monic quadratic are integral.

This isolates the proper chart for the remaining nonsplit degree-two
graph without constructing its splitting field or enumerating quadratic
extensions.
-/
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- Coefficient form of a monic quadratic. -/
theorem monic_quadratic_eq
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have hc₂ : p.coeff 2 = 1 := by
    calc
      p.coeff 2 = p.coeff p.natDegree :=
        congrArg p.coeff hdeg.symm
      _ = 1 := hp.coeff_natDegree
  have hpDegreeLe : p.degree ≤ 2 := by
    rw [degree_eq_natDegree hp.ne_zero, hdeg]
    norm_num
  calc
    p =
        C (p.coeff 2) * X ^ 2 +
          C (p.coeff 1) * X +
          C (p.coeff 0) :=
      p.eq_quadratic_of_degree_le_two hpDegreeLe
    _ = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      rw [hc₂, C_1]
      ring
end
end MazurProof.N13IrreducibleQuadraticChart
end

end

-- ===== FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction =====
section
-- ===== FLT.Assumptions.MazurProof.N13ReciprocalInfinityContraction =====
section
/-!
# The reciprocal N13 divisor on the integral infinity chart

For a quadratic generic Mumford graph with nonzero constant coefficient,
the class of the affine coordinate is invertible in its graph quotient.
Its explicit inverse is the infinity coordinate `t`, and `t³y` is the
ordinary infinity ordinate.  The ordinary overlap identity therefore
defines a canonical map from the integral infinity chart into the original
generic Mumford quotient.  Its kernel is the integral infinity ideal used
for rank-two recovery.
-/
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.baseSpecialAlgebra
theorem xbar_quadratic
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    xbar D ^ 2 +
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) *
          xbar D +
        algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0) = 0 := by
  have hu :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model D.u) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (SexticMumford.xClass_mem_mumfordIdeal
        Model D.toSemi.u D.toSemi.v)
  have hshape :=
    N13IrreducibleQuadraticChart.monic_quadratic_eq
      D.u D.u_monic hdeg
  have hxshape :
      SexticMumford.xClass Model D.u =
        SexticMumford.xClass Model X ^ 2 +
          SexticMumford.xClass Model (C (D.u.coeff 1)) *
            SexticMumford.xClass Model X +
          SexticMumford.xClass Model (C (D.u.coeff 0)) := by
    rw [hshape]
    simp [SexticMumford.xClass, SexticMumford.mk]
  rw [hxshape] at hu
  simp only [map_add, map_mul, map_pow] at hu
  have hC (c : Q₂) :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model (C c)) =
        algebraMap Q₂ (GenericQuotient D) c := by
    rfl
  rw [hC, hC] at hu
  simpa only [xbar] using hu
theorem xbar_mul_tbar
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    xbar D * tbar D = 1 := by
  have hu := xbar_quadratic D hdeg
  let u0 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)
  let u0i : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹)
  have hunit : u0i * u0 = 1 := by
    dsimp only [u0i, u0]
    rw [← map_mul]
    simp [h0]
  dsimp only [tbar]
  rw [map_neg]
  change
    xbar D *
        (-u0i *
          (xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1))) =
      1
  linear_combination -u0i * hu + hunit
end
end MazurProof.N13ReciprocalInfinityContraction
end

end

theorem solution : type_of% @MazurProof.N13ReciprocalInfinityContraction.xbar_mul_tbar := @MazurProof.N13ReciprocalInfinityContraction.xbar_mul_tbar
