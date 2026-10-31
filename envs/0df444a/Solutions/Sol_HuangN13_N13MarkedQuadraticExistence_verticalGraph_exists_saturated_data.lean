-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:53:40.905621+00:00
-- url     : https://prove2.me/submissions/9ab9e284-f7b8-4016-bf02-87fd6965c163

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13IntegralInfinityVerticalGraphSpecialRestriction_exists_specialDivisor
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_goodYInSextic_root
import Theorems.Thm_MazurProof_N13ReciprocalInfinityContraction_xbar_mul_tbar

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toSextic_yClass :
    toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  AdjoinRoot.lift_root (MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralModelContraction.integralRationalAlgebra MazurProof.N13IntegralModelContraction.rationalRingLocalization
/-- The contracted ideal is saturated with respect to every nonzero
vertical scalar. -/
theorem contractIdeal_vertical_saturated
    (J : Ideal RationalRing)
    {a : IntegralRing}
    (r : R₂) (hr : r ≠ 0)
    (ha :
      algebraMap R₂ IntegralRing r * a ∈
        contractIdeal J) :
    a ∈ contractIdeal J := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (algebraMap R₂ IntegralRing r * a) ∈ J at ha
  rw [map_mul] at ha
  let s : verticalScalars :=
    ⟨algebraMap R₂ IntegralRing r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩
  have hs :
      IsUnit
        (algebraMap IntegralRing RationalRing s) :=
    IsLocalization.map_units RationalRing s
  exact (Ideal.unit_mul_mem_iff_mem J hs).mp ha
end
end MazurProof.N13IntegralModelContraction
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
/-- Extending the kernel of a map across a localization gives the kernel
of any compatible map out of the localized ring. -/
theorem map_ker_eq_ker_of_isLocalization
    {C : Type*} [CommRing C]
    (f : A →+* C)
    (g : B →+* C)
    (hcomp :
      g.comp (algebraMap A B) = f) :
    Ideal.map (algebraMap A B) (RingHom.ker f) =
      RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change g (algebraMap A B a) = 0
    rw [← RingHom.comp_apply, hcomp, ha]
  · intro z hz
    obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj M z
    have ha : a ∈ RingHom.ker f := by
      rw [RingHom.mem_ker]
      have hzero := congrArg g hzs
      rw [map_mul, RingHom.mem_ker.mp hz, zero_mul,
        ← RingHom.comp_apply, hcomp] at hzero
      exact hzero.symm
    have hma :
        algebraMap A B a ∈
          Ideal.map (algebraMap A B) (RingHom.ker f) :=
      Ideal.mem_map_of_mem (algebraMap A B) ha
    have hzsMem :
        z * algebraMap A B (s : A) ∈
          Ideal.map (algebraMap A B) (RingHom.ker f) := by
      rw [hzs]
      exact hma
    exact
      (Ideal.unit_mul_mem_iff_mem
        (Ideal.map (algebraMap A B) (RingHom.ker f))
        (IsLocalization.map_units B s)).mp
          (by simpa [mul_comm] using hzsMem)
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem mem_of_x_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := hx
  have h₁ := Ideal.mul_mem_left I z hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1 <;> ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem mem_of_x_pow_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    (n : ℕ) {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_x_mul_mem hx
      convert hz using 1 <;> simp only [pow_succ] <;> ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Localizing at `x` loses no ideal information when `x` is already a
unit modulo the ideal. -/
theorem comap_map_affineOverlap_eq_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap)
        (Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z ∈
        Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_x_pow_mul_mem hx n hmz
  · exact Ideal.le_comap_map
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The actual affine-to-infinity overlap map is the localization map
followed by the chart equivalence. -/
private theorem affineToInfinityOverlap_eq_comp :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13OrdinaryCurveOverlap.overlapEquiv.toRingHom.comp
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap) := by
  apply DFunLike.ext _ _
  intro z
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap z =
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z)
  exact
    (N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap
      z).symm
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction to the actual ordinary overlap loses no information from
an affine ideal when `x` is already a unit modulo that ideal. -/
theorem affineOverlapContracted_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I) =
      I := by
  let loc :
      AffineCurve →+*
        N13OrdinaryCurveOverlap.AffineOverlap :=
    algebraMap AffineCurve
      N13OrdinaryCurveOverlap.AffineOverlap
  let e :
      N13OrdinaryCurveOverlap.AffineOverlap →+*
        InfinityOverlap :=
    N13OrdinaryCurveOverlap.overlapEquiv.toRingHom
  have he :
      Ideal.comap e (Ideal.map e (Ideal.map loc I)) =
        Ideal.map loc I := by
    rw [Ideal.comap_map_of_surjective e
      N13OrdinaryCurveOverlap.overlapEquiv.surjective]
    have hker : RingHom.ker e = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e).mp
        N13OrdinaryCurveOverlap.overlapEquiv.injective
    rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq]
  rw [affineToInfinityOverlap_eq_comp,
    ← Ideal.map_map, ← Ideal.comap_comap, he]
  exact comap_map_affineOverlap_eq_of_xUnitMod hx
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- Coefficient form of a monic quadratic. -/
theorem monic_quadratic_eq
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + _root_.Polynomial.C (p.coeff 1) * X + _root_.Polynomial.C (p.coeff 0) := by
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
        _root_.Polynomial.C (p.coeff 2) * X ^ 2 +
          _root_.Polynomial.C (p.coeff 1) * X +
          _root_.Polynomial.C (p.coeff 0) :=
      p.eq_quadratic_of_degree_le_two hpDegreeLe
    _ = X ^ 2 + _root_.Polynomial.C (p.coeff 1) * X + _root_.Polynomial.C (p.coeff 0) := by
      rw [hc₂, C_1]
      ring
end
end MazurProof.N13IrreducibleQuadraticChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
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
          SexticMumford.xClass Model (_root_.Polynomial.C (D.u.coeff 1)) *
            SexticMumford.xClass Model X +
          SexticMumford.xClass Model (_root_.Polynomial.C (D.u.coeff 0)) := by
    rw [hshape]
    simp [SexticMumford.xClass, SexticMumford.mk]
  rw [hxshape] at hu
  simp only [map_add, map_mul, map_pow] at hu
  have hC (c : Q₂) :
      Ideal.Quotient.mk (genericIdeal D)
          (SexticMumford.xClass Model (_root_.Polynomial.C c)) =
        algebraMap Q₂ (GenericQuotient D) c := by
    rfl
  rw [hC, hC] at hu
  simpa only [xbar] using hu
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem infinityCurve_root
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        (baseToGenericQuotient D) (vbar D) = 0 := by
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul, sub_eq_zero]
  simpa [baseToGenericQuotient, coefficientToGenericQuotient,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] using
      vbar_relation D hdeg h0
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_tClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    integralInfinityToGenericQuotient D hdeg h0
        N13IntegralInfinityChart.tClass = tbar D := by
  simp [integralInfinityToGenericQuotient,
    N13IntegralInfinityChart.tClass, baseToGenericQuotient]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_vClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    integralInfinityToGenericQuotient D hdeg h0
        N13IntegralInfinityChart.vClass = vbar D :=
  AdjoinRoot.lift_root (infinityCurve_root D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_xClass
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (p : R₂[X]) :
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      baseToGenericQuotient D p := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) = _
  exact AdjoinRoot.lift_of (infinityCurve_root D hdeg h0)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralInfinityToGenericQuotient_algebraMap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (r : R₂) :
    integralInfinityToGenericQuotient D hdeg h0
        (algebraMap R₂ InfinityRing r) =
      algebraMap Q₂ (GenericQuotient D)
        (N13TwoAdicCoordinateBaseChange.coeffMap r) := by
  change
    integralInfinityToGenericQuotient D hdeg h0
        (N13IntegralInfinityGraphJacobian.xClassHom (_root_.Polynomial.C r)) = _
  rw [integralInfinityToGenericQuotient_xClass]
  simp [baseToGenericQuotient, coefficientToGenericQuotient]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem baseToGenericQuotient_eq_aeval_mapPoly
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    baseToGenericQuotient D p =
      aeval (tbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) := by
  change
    p.eval₂
        ((algebraMap Q₂ (GenericQuotient D)).comp
          N13TwoAdicCoordinateBaseChange.coeffMap)
        (tbar D) =
      (p.map N13TwoAdicCoordinateBaseChange.coeffMap).eval₂
        (algebraMap Q₂ (GenericQuotient D)) (tbar D)
  exact
    (Polynomial.eval₂_map
      (p := p)
      N13TwoAdicCoordinateBaseChange.coeffMap
      (algebraMap Q₂ (GenericQuotient D))
      (tbar D)).symm
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem reciprocal_aeval_tbar_eq_zero
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + _root_.Polynomial.C (a : Q₂) * X + _root_.Polynomial.C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          _root_.Polynomial.C (D.u.coeff 1 / D.u.coeff 0) * X +
          _root_.Polynomial.C ((D.u.coeff 0)⁻¹)) :
    aeval (tbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly
          (N13ReciprocalQuadraticReflection.integralReciprocal a b)) =
      0 := by
  have hu := xbar_quadratic D hdeg
  have htx : tbar D * xbar D = 1 := by
    simpa [mul_comm] using xbar_mul_tbar D hdeg h0
  let u0 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)
  let u0i : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) ((D.u.coeff 0)⁻¹)
  let u1 : GenericQuotient D :=
    algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1)
  have hunit : u0i * u0 = 1 := by
    dsimp only [u0i, u0]
    rw [← map_mul]
    simp [h0]
  have hmapm :
      N13TwoAdicCoordinateBaseChange.mapPoly
          (N13ReciprocalQuadraticReflection.integralReciprocal a b) =
        X ^ 2 +
          _root_.Polynomial.C (D.u.coeff 1 / D.u.coeff 0) * X +
          _root_.Polynomial.C ((D.u.coeff 0)⁻¹) := by
    simpa [N13ReciprocalQuadraticReflection.integralReciprocal,
      N13TwoAdicCoordinateBaseChange.mapPoly,
      N13TwoAdicCoordinateBaseChange.coeffMap,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap] using hm
  rw [hmapm]
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  change
    tbar D ^ 2 +
        (algebraMap Q₂ (GenericQuotient D)
          (D.u.coeff 1 / D.u.coeff 0)) * tbar D +
        u0i = 0
  rw [div_eq_mul_inv, map_mul]
  change tbar D ^ 2 + u1 * u0i * tbar D + u0i = 0
  calc
    tbar D ^ 2 + u1 * u0i * tbar D + u0i =
        u0i * tbar D ^ 2 *
          (xbar D ^ 2 + u1 * xbar D + u0) := by
      calc
        _ =
            u0i * (tbar D * xbar D) ^ 2 +
              u0i * u1 * tbar D * (tbar D * xbar D) +
              (u0i * u0) * tbar D ^ 2 := by
                rw [htx, hunit]
                ring
        _ = _ := by ring
    _ = 0 := by
      change
        u0i * tbar D ^ 2 *
          (xbar D ^ 2 +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 1) *
              xbar D +
            algebraMap Q₂ (GenericQuotient D) (D.u.coeff 0)) = 0
      simpa [hu]
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem reciprocal_mem_integralInfinityIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + _root_.Polynomial.C (a : Q₂) * X + _root_.Polynomial.C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          _root_.Polynomial.C (D.u.coeff 1 / D.u.coeff 0) * X +
          _root_.Polynomial.C ((D.u.coeff 0)⁻¹)) :
    N13IntegralInfinityGraphJacobian.xClassHom
        (N13ReciprocalQuadraticReflection.integralReciprocal a b) ∈
      integralInfinityIdeal D hdeg h0 := by
  rw [integralInfinityIdeal, RingHom.mem_ker]
  rw [integralInfinityToGenericQuotient_xClass]
  rw [baseToGenericQuotient_eq_aeval_mapPoly]
  exact reciprocal_aeval_tbar_eq_zero D hdeg h0 a b hm
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem aeval_mapPoly_xbar
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    aeval (xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) =
      p.eval₂ (coefficientToGenericQuotient D) (xbar D) := by
  change
    (p.map N13TwoAdicCoordinateBaseChange.coeffMap).eval₂
        (algebraMap Q₂ (GenericQuotient D)) (xbar D) =
      p.eval₂
        ((algebraMap Q₂ (GenericQuotient D)).comp
          N13TwoAdicCoordinateBaseChange.coeffMap)
        (xbar D)
  exact
    Polynomial.eval₂_map
      (p := p)
      N13TwoAdicCoordinateBaseChange.coeffMap
      (algebraMap Q₂ (GenericQuotient D))
      (xbar D)
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
namespace MazurProof.N13ReciprocalInfinityContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem aeval_xbar
    (D : SexticMumford.Mumford Model)
    (p : Q₂[X]) :
    aeval (xbar D) p =
      Ideal.Quotient.mk (genericIdeal D)
        (SexticMumford.xClass Model p) := by
  let ψ : Q₂[X] →ₐ[Q₂] GenericQuotient D :=
    IsScalarTower.toAlgHom Q₂ Q₂[X] (GenericQuotient D)
  have h :
      aeval (xbar D) = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun h p
end
end MazurProof.N13ReciprocalInfinityContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The reciprocal infinity coordinate maps to a unit in the original
generic Mumford quotient. -/
theorem tbar_isUnit
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    IsUnit (N13ReciprocalInfinityContraction.tbar D) := by
  apply isUnit_iff_exists_inv.mpr
  exact
    ⟨N13ReciprocalInfinityContraction.xbar D,
      by
        simpa [mul_comm] using
          N13ReciprocalInfinityContraction.xbar_mul_tbar
            D hdeg h0⟩
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extension of the direct infinity-chart map to the ordinary overlap. -/
def infinityOverlapToGenericQuotient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    InfinityOverlap →+* GenericQuotient D :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    (by
      rw [
        N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass
          D hdeg h0]
      exact tbar_isUnit D hdeg h0)
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The overlap extension restricts to the original direct infinity map. -/
@[simp] theorem infinityOverlapToGenericQuotient_comp_infinity
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (infinityOverlapToGenericQuotient D hdeg h0).comp
        (algebraMap InfinityCurve InfinityOverlap) =
      N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient
        D hdeg h0 := by
  exact
    IsLocalization.Away.lift_comp
      N13IntegralInfinityChart.tClass
      (by
        rw [
          N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass
            D hdeg h0]
        exact tbar_isUnit D hdeg h0)
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The named overlap coordinate `t` maps to the reciprocal quotient
coordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_tOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.tOverlap =
      N13ReciprocalInfinityContraction.tbar D := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    ← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_tClass]
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The named overlap coordinate `v` maps to the reciprocal quotient
ordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_vOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.vOverlap =
      N13ReciprocalInfinityContraction.vbar D := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    ← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_vClass]
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The inverse overlap coordinate `x=t⁻¹` maps to the affine quotient
coordinate. -/
@[simp] theorem infinityOverlapToGenericQuotient_xOverlap
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    infinityOverlapToGenericQuotient D hdeg h0
        N13OrdinaryCurveOverlap.xOverlap =
      N13ReciprocalInfinityContraction.xbar D := by
  let φ :=
    infinityOverlapToGenericQuotient D hdeg h0
  have htx :
      N13ReciprocalInfinityContraction.tbar D *
          φ N13OrdinaryCurveOverlap.xOverlap =
        1 := by
    calc
      N13ReciprocalInfinityContraction.tbar D *
            φ N13OrdinaryCurveOverlap.xOverlap =
          φ N13OrdinaryCurveOverlap.tOverlap *
            φ N13OrdinaryCurveOverlap.xOverlap := by
              rw [infinityOverlapToGenericQuotient_tOverlap]
      _ =
          φ
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by rw [map_mul]
      _ = 1 := by
        rw [N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap, map_one]
  calc
    φ N13OrdinaryCurveOverlap.xOverlap =
        1 * φ N13OrdinaryCurveOverlap.xOverlap := by simp
    _ =
        (N13ReciprocalInfinityContraction.xbar D *
            N13ReciprocalInfinityContraction.tbar D) *
          φ N13OrdinaryCurveOverlap.xOverlap := by
            rw [
              N13ReciprocalInfinityContraction.xbar_mul_tbar
                D hdeg h0]
    _ = N13ReciprocalInfinityContraction.xbar D := by
      rw [mul_assoc, htx, mul_one]
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Integral coefficients on the overlap map to their images in the
generic Mumford quotient. -/
@[simp] theorem infinityOverlapToGenericQuotient_coefficient
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (r : R₂) :
    infinityOverlapToGenericQuotient D hdeg h0
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r) =
      N13ReciprocalInfinityContraction.coefficientToGenericQuotient
        D r := by
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    infinityOverlapToGenericQuotient D hdeg h0
        ((algebraMap InfinityCurve InfinityOverlap)
          (algebraMap R₂ InfinityCurve r)) =
      _
  rw [← RingHom.comp_apply,
    infinityOverlapToGenericQuotient_comp_infinity,
    N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient_algebraMap]
  rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine horizontal polynomial class evaluates at the quotient
coordinate `x̄`. -/
@[simp] theorem affineToGenericQuotient_xClassHom
    (D : SexticMumford.Mumford Model)
    (p : R₂[X]) :
    affineToGenericQuotient D
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      aeval (N13ReciprocalInfinityContraction.xbar D)
        (N13TwoAdicCoordinateBaseChange.mapPoly p) := by
  change
    Ideal.Quotient.mk
        (N13ReciprocalInfinityContraction.genericIdeal D)
        (N13GoodSexticCoordinateEquiv.toSextic
          (N13TwoAdicCoordinateBaseChange.extendCoordinate
            (N13GeneralizedMumfordIntegral.xClass p))) =
      _
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass]
  exact
    (N13ReciprocalInfinityContraction.aeval_xbar
      D (N13TwoAdicCoordinateBaseChange.mapPoly p)).symm
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine integral ordinate maps to the good-model ordinate in the
generic Mumford quotient. -/
@[simp] theorem affineToGenericQuotient_yClass
    (D : SexticMumford.Mumford Model) :
    affineToGenericQuotient D
        N13GeneralizedMumfordIntegral.yClass =
      N13ReciprocalInfinityContraction.goodYbar D := by
  rw [affineToGenericQuotient, RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.extend_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_yClass]
  rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine and infinity descriptions of the direct map agree on the
ordinary overlap. -/
theorem overlap_affine_map_compatibility
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    (infinityOverlapToGenericQuotient D hdeg h0).comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      affineToGenericQuotient D := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineToInfinityOverlap_of]
      change
        infinityOverlapToGenericQuotient D hdeg h0
            (N13OrdinaryCurveOverlap.affineCoeffMap (_root_.Polynomial.C r)) =
          affineToGenericQuotient D
            (N13GeneralizedMumfordIntegral.xClassHom (_root_.Polynomial.C r))
      rw [N13OrdinaryCurveOverlap.affineCoeffMap_C,
        infinityOverlapToGenericQuotient_coefficient,
        affineToGenericQuotient_xClassHom,
        N13ReciprocalInfinityContraction.aeval_mapPoly_xbar]
      simp [N13ReciprocalInfinityContraction.coefficientToGenericQuotient]
    · change
        ((infinityOverlapToGenericQuotient D hdeg h0).comp
            N13OrdinaryCurveOverlap.affineToInfinityOverlap)
            (N13GeneralizedMumfordIntegral.xClassHom X) =
          affineToGenericQuotient D
            (N13GeneralizedMumfordIntegral.xClassHom X)
      rw [RingHom.comp_apply,
        N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
        N13OrdinaryCurveOverlap.affineCoeffMap_X]
      rw [infinityOverlapToGenericQuotient_xOverlap,
        affineToGenericQuotient_xClassHom]
      simp [N13TwoAdicCoordinateBaseChange.mapPoly]
  · change
      ((infinityOverlapToGenericQuotient D hdeg h0).comp
          N13OrdinaryCurveOverlap.affineToInfinityOverlap)
          N13GeneralizedMumfordIntegral.yClass =
        affineToGenericQuotient D
          N13GeneralizedMumfordIntegral.yClass
    rw [RingHom.comp_apply,
      N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass]
    rw [N13OrdinaryCurveOverlap.affineYImage,
      map_mul, map_pow,
      infinityOverlapToGenericQuotient_xOverlap,
      infinityOverlapToGenericQuotient_vOverlap,
      affineToGenericQuotient_yClass]
    change
      N13ReciprocalInfinityContraction.xbar D ^ 3 *
          (N13ReciprocalInfinityContraction.tbar D ^ 3 *
            N13ReciprocalInfinityContraction.goodYbar D) =
        N13ReciprocalInfinityContraction.goodYbar D
    rw [← mul_assoc, ← mul_pow,
      N13ReciprocalInfinityContraction.xbar_mul_tbar D hdeg h0,
      one_pow, one_mul]
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The kernel of the overlap map is the extension of the direct integral
infinity kernel. -/
theorem map_integralInfinityIdeal_eq_overlapKernel
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0) =
      RingHom.ker
        (infinityOverlapToGenericQuotient D hdeg h0) := by
  rw [N13ReciprocalInfinityContraction.integralInfinityIdeal]
  exact
    N13LocalizationIdealPatch.map_ker_eq_ker_of_isLocalization
      (A := InfinityCurve) (B := InfinityOverlap)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      (N13ReciprocalInfinityContraction.integralInfinityToGenericQuotient
        D hdeg h0)
      (infinityOverlapToGenericQuotient D hdeg h0)
      (infinityOverlapToGenericQuotient_comp_infinity D hdeg h0)
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The kernel of the affine quotient map is the canonical contraction of
the original generic Mumford ideal. -/
theorem affineToGenericQuotient_ker
    (D : SexticMumford.Mumford Model) :
    RingHom.ker (affineToGenericQuotient D) =
      N13IntegralModelContraction.contractIdeal
        (N13ReciprocalInfinityContraction.genericIdeal D) := by
  change
    RingHom.ker
        ((Ideal.Quotient.mk
          (N13ReciprocalInfinityContraction.genericIdeal D)).comp
          N13TwoAdicCoordinateBaseChange.integralToSextic) =
      Ideal.comap
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13ReciprocalInfinityContraction.genericIdeal D)
  rw [← RingHom.comap_ker, Ideal.mk_ker]
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A recovered vertical graph gives exactly the canonical affine
contraction of the original generic Mumford ideal. -/
theorem contractIdeal_eq_affineIdeal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    N13IntegralModelContraction.contractIdeal
        (N13ReciprocalInfinityContraction.genericIdeal D) =
      N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E := by
  let Ia :=
    N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E
  let f :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g : InfinityCurve →+* InfinityOverlap :=
    algebraMap InfinityCurve InfinityOverlap
  let q :=
    infinityOverlapToGenericQuotient D hdeg h0
  calc
    N13IntegralModelContraction.contractIdeal
          (N13ReciprocalInfinityContraction.genericIdeal D) =
        RingHom.ker (affineToGenericQuotient D) :=
      (affineToGenericQuotient_ker D).symm
    _ = Ideal.comap f (RingHom.ker q) := by
      rw [RingHom.comap_ker,
        overlap_affine_map_compatibility D hdeg h0]
    _ =
        Ideal.comap f
          (Ideal.map g
            (N13ReciprocalInfinityContraction.integralInfinityIdeal
              D hdeg h0)) := by
      rw [map_integralInfinityIdeal_eq_overlapKernel D hdeg h0]
    _ = Ideal.comap f (Ideal.map g E.ideal) := by rw [hI]
    _ = Ideal.comap f (Ideal.map f Ia) := by
      rw [
        N13IntegralInfinityVerticalGraphTwoChart.ideals_agree_on_overlap
          u E huDegree.le hmDegree huMem]
    _ = Ia := by
      exact
        N13IntegralInfinityGraphSaturation.affineOverlapContracted_of_xUnitMod
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_xUnitMod
            u E hu huDegree)
end
end MazurProof.N13IntegralInfinityVerticalGraphContraction
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A line whose affine lattice is a canonical generic-fibre contraction is
vertically saturated. -/
theorem affineVerticallySaturated_of_affineIdeal_eq_contractIdeal
    (L : Line)
    (J : Ideal N13IntegralModelContraction.RationalRing)
    (hL :
      L.affineIdeal =
        N13IntegralModelContraction.contractIdeal J) :
    AffineVerticallySaturated L := by
  intro r hr a ha
  rw [hL] at ha ⊢
  exact
    N13IntegralModelContraction.contractIdeal_vertical_saturated
      J r hr ha
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralFunctionFieldFractionRing MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coercing the generic ideal unit to a fractional ideal recovers the
literal extension of the line's affine ideal.

This bridge is independent of the geometric origin of the proper line and is
therefore shared by point and quadratic Picard realizations. -/
@[simp] theorem coe_genericIdealUnit
    (L : Line) :
    (genericIdealUnit L :
        N13IntegralFractionalHull.RationalFractionalIdeal) =
      (Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal :
        N13IntegralFractionalHull.RationalFractionalIdeal) := by
  change
    N13IntegralFractionalHull.extendFractional
        (L.affine_isUnit.unit :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      _
  rw [L.affine_isUnit.unit_spec,
    N13IntegralFractionalHull.extendFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Equality of mapped generic affine ideals determines equality of their
packaged fractional-ideal units.

The statement retains the exact Mumford representative rather than passing
prematurely to the oriented Picard quotient. -/
theorem genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericIdealUnit L =
      SexticMumford.mumfordIdealUnit Model D.toSemi := by
  apply Units.ext
  rw [coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      hmap
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A proper line with the exact Mumford affine ideal realizes the literal
oriented Mumford datum when marked by the representative's exponent
`nInf - 1`.

This is the generic-fibre bridge used uniformly by point and quadratic
two-chart realizations. -/
theorem genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericRaw L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D := by
  apply Prod.ext
  · exact
      genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
        L D hmap
  · rfl
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact mapped-ideal equality also identifies the induced generic Picard
class with the standard oriented class of the Mumford representative. -/
theorem genericClass_eq_classOf_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericClass L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        D := by
  unfold genericClass SexticMumford.classOf
  rw [genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq L D hmap]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
/-- Proper two-chart lines on the integral good model. -/
abbrev Line : Type :=
  N13TwoChartPicardRealization.Line
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Package one proper line and its two exact special chart comparisons as
two-fibre Picard data for a chosen Mumford representative.

The generic affine ideal equality is not needed to construct the data; it is
consumed separately to identify the resulting generic class. -/
def dataOfSpecialRealization
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal) :
    N13TwoChartPicardRealization.Data where
  charts := L
  infinityOrder := (D.nInf : ℤ) - 1
  specialDivisor := Δ
  special_affine := haffine
  special_infinity := hinfinity
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Packaging a line with its special divisor does not alter its affine
lattice, so a vertical-saturation certificate passes through definitionally. -/
theorem dataOfSpecialRealization_affineVerticallySaturated
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (dataOfSpecialRealization D L Δ haffine hinfinity).charts := by
  exact hL
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact generic affine-ideal equality identifies the raw generic datum of
`dataOfSpecialRealization` with the literal Mumford raw datum. -/
theorem dataOfSpecialRealization_genericRaw_eq_mumfordRaw
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    N13TwoChartPicardRealization.genericRaw
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).charts
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).infinityOrder =
      SexticMumford.mumfordRaw Model D := by
  change
    N13TwoChartPicardRealization.genericRaw
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D
  exact
    N13TwoChartPicardRealization.genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
      L D hmap
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic Picard class of the packaged realization is the standard
oriented class of the same Mumford representative. -/
theorem dataOfSpecialRealization_toGenericPic_eq_classOf
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    (dataOfSpecialRealization
      D L Δ haffine hinfinity).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D := by
  change
    N13TwoChartPicardRealization.genericClass
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D
  exact
    N13TwoChartPicardRealization.genericClass_eq_classOf_of_map_affineIdeal_eq
      L D hmap
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalVerticalGraphPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A recovered vertical reciprocal graph gives a vertically saturated
proper affine lattice.  The contraction theorem identifies that lattice
with the canonical contraction of the original generic Mumford ideal, where
nonzero base scalars cancel by localization. -/
theorem verticalGraph_twoChartLine_affineVerticallySaturated
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (u : N13IrreducibleQuadraticSpread.R₂[X])
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
        u E hu huDegree hmDegree huMem) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_contractIdeal
      _ (N13ReciprocalInfinityContraction.genericIdeal D)
  exact
    (N13IntegralInfinityVerticalGraphContraction.contractIdeal_eq_affineIdeal
      D hdeg h0 u E hu huDegree hmDegree huMem hI).symm
end
end MazurProof.N13ReciprocalVerticalGraphPicardRealization
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem positiveExpansion_base (p : N13IntegralInfinityChart.Base) :
    positiveExpansion (N13IntegralInfinityPointSpread.xClassHom p) =
      N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p) := by
  simp [positiveExpansion, positiveIntegralExpansion,
    N13IntegralInfinityPointSpread.xClassHom, N13IntegralInfinityChart.toFormalInfinity,
    N13FormalInfinitySplit.evalBranchZero]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem negativeExpansion_base (p : N13IntegralInfinityChart.Base) :
    negativeExpansion (N13IntegralInfinityPointSpread.xClassHom p) =
      N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p) := by
  simp [negativeExpansion, negativeIntegralExpansion,
    N13IntegralInfinityPointSpread.xClassHom, N13IntegralInfinityChart.toFormalInfinity,
    N13FormalInfinitySplit.evalBranchOne]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem generic_base_constantCoeff (p : N13IntegralInfinityChart.Base) :
    PowerSeries.constantCoeff
      (N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p)) =
      N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    cases n <;> simp [N13IntegralInfinityChart.baseToPower,
      N13TwoAdicInfinityCompatibility.powerMap]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem map_top_of_polynomial_mem
    (f : B →+* QP)
    (hf : ∀ p : N13IntegralInfinityChart.Base,
      f (N13IntegralInfinityPointSpread.xClassHom p) =
        N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p))
    (I : Ideal B) (p : N13IntegralInfinityChart.Base)
    (hp : N13IntegralInfinityPointSpread.xClassHom p ∈ I)
    (hp0 : N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) ≠ 0) :
    Ideal.map f I = ⊤ := by
  have hm := Ideal.mem_map_of_mem f hp
  have hu : IsUnit (f (N13IntegralInfinityPointSpread.xClassHom p)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hf, generic_base_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hp0
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left (Ideal.map f I) (↑(u⁻¹) : QP) hm
  simpa using hh
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A horizontal polynomial with nonzero generic constant term is enough
to certify that the actual infinity ideal has no generic infinity support.
This applies equally to horizontal and vertical reciprocal graph charts. -/
theorem marked_of_polynomial_mem
    (L : Line) (p : N13IntegralInfinityChart.Base)
    (hp : N13IntegralInfinityPointSpread.xClassHom p ∈ L.infinityIdeal)
    (hp0 : N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) ≠ 0) :
    HasInfinityMultiplicities L 0 0 := by
  constructor
  · simpa only [pow_zero, Ideal.span_singleton_one] using
      map_top_of_polynomial_mem positiveExpansion positiveExpansion_base L.infinityIdeal p hp hp0
  · simpa only [pow_zero, Ideal.span_singleton_one] using
      map_top_of_polynomial_mem negativeExpansion negativeExpansion_base L.infinityIdeal p hp hp0
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityVerticalGraphLine_marked
    (u : Polynomial N13IrreducibleQuadraticSpread.R₂)
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hu : u.Monic) (huDegree : u.natDegree = 2) (hmDegree : E.m.natDegree = 2)
    (huMem : N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (h0 : N13TwoAdicInfinityCompatibility.coeffMap (u.coeff 0) ≠ 0) :
    HasInfinityMultiplicities
      (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine u E hu huDegree hmDegree huMem) 0 0 := by
  exact marked_of_polynomial_mem _ u huMem h0
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The nonzero-constant premise of the reciprocal chart marking follows
from the actual reciprocal equation already carried by that construction. -/
theorem reciprocal_constant_nonzero
    (D : N13Mumford.Mumford N13TwoChartPicardRealization.Q₂)
    (a b : N13IrreducibleQuadraticSpread.R₂)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm : (X ^ 2 + _root_.Polynomial.C (a : N13TwoChartPicardRealization.Q₂) * X +
        _root_.Polynomial.C (b : N13TwoChartPicardRealization.Q₂)) =
      X ^ 2 + _root_.Polynomial.C (D.u.coeff 1 / D.u.coeff 0) * X + _root_.Polynomial.C ((D.u.coeff 0)⁻¹)) :
    N13TwoAdicInfinityCompatibility.coeffMap
      ((N13ReciprocalQuadraticReflection.integralReciprocal a b).coeff 0) ≠ 0 := by
  have hb : (b : N13TwoChartPicardRealization.Q₂) = (D.u.coeff 0)⁻¹ := by
    simpa using congrArg (fun p => p.coeff 0) hm
  have hc : (N13ReciprocalQuadraticReflection.integralReciprocal a b).coeff 0 = b := by
    simp [N13ReciprocalQuadraticReflection.integralReciprocal]
  rw [hc]
  change (b : N13TwoChartPicardRealization.Q₂) ≠ 0
  rw [hb]
  exact inv_ne_zero h0
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem verticalGraph_exists_saturated_data
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          _root_.Polynomial.C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          _root_.Polynomial.C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          _root_.Polynomial.C (D.u.coeff 1 / D.u.coeff 0) * X +
          _root_.Polynomial.C ((D.u.coeff 0)⁻¹))
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  let u :=
    N13ReciprocalQuadraticReflection.integralReciprocal a b
  have hu : u.Monic :=
    N13ReciprocalQuadraticReflection.integralReciprocal_monic a b
  have huDegree : u.natDegree = 2 :=
    N13ReciprocalQuadraticReflection.integralReciprocal_natDegree a b
  have huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal := by
    rw [← hI]
    exact
      N13ReciprocalInfinityContraction.reciprocal_mem_integralInfinityIdeal
        D hdeg h0 a b hm
  let L :=
    N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
      u E hu huDegree hmDegree huMem
  obtain ⟨Δ, hrestrict⟩ :=
    HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
      u E hu huDegree hmDegree huMem
  have haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal :=
    congrArg (fun C => C.affineIdeal) hrestrict
  have hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal :=
    congrArg (fun C => C.infinityIdeal) hrestrict
  have hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v := by
    change
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E) =
        N13ReciprocalInfinityContraction.genericIdeal D
    rw [←
        N13IntegralInfinityVerticalGraphContraction.contractIdeal_eq_affineIdeal
          D hdeg h0 u E hu huDegree hmDegree huMem hI,
      N13IntegralModelContraction.map_contractIdeal]
  let R :=
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization
      D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity
        (N13ReciprocalVerticalGraphPicardRealization.verticalGraph_twoChartLine_affineVerticallySaturated
          hdeg h0 u E hu huDegree hmDegree huMem hI)
  · exact infinityVerticalGraphLine_marked u E hu huDegree hmDegree huMem
      (reciprocal_constant_nonzero D a b h0 hm)
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    {D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model}
    {a b : MazurProof.N13IrreducibleQuadraticSpread.R₂}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) :
        MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹))
    (E : MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw
          MazurProof.N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13IrreducibleQuadraticSpread.Model
          (MazurProof.N13Infinity.positiveInfinityOrder
            MazurProof.N13TwoChartPicardRealization.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data hdeg h0 hm E hmDegree hI
