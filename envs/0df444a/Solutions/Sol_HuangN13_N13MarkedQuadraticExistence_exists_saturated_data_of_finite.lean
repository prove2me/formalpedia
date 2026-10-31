-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:36:58.34+00:00
-- url     : https://prove2.me/submissions/cc08d773-fc64-4336-85c1-e9b45c9561d3

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_HuangN13_N13FiniteQuadraticSpecialRestriction_exists_specialDivisor_of_finiteQuadratic
import Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_finiteAffineIdeal_isUnit
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap

set_option autoImplicit false

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
open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13ConcreteGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Evaluation at the integral affine `x` coordinate is the coordinate
embedding of the polynomial subring. -/
@[simp] theorem aeval_integralX (p : R₂[X]) :
    aeval N13CanonicalContractionQuotient.integralX p =
      N13GeneralizedMumfordIntegral.xClass (R := R₂) p := by
  change
    aeval
        (algebraMap R₂[X] IntegralRing X) p =
      algebraMap R₂[X] IntegralRing p
  simpa using
    aeval_algebraMap_apply IntegralRing
      (X : R₂[X]) p
end
end MazurProof.N13ConcreteGraphRecovery
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13ConcreteGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Polynomial evaluation commutes with passage to any quotient of the
integral affine ring. -/
theorem quotient_aeval_integralX
    (I : Ideal IntegralRing) (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) p =
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) := by
  rw [← aeval_integralX]
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := IntegralRing) (T := R₂)
      (U := IntegralRing ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13CanonicalContractionQuotient.integralX).symm
end
end MazurProof.N13ConcreteGraphRecovery
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extending the canonical affine lattice to the generic coefficient field
recovers the Mumford graph ideal literally. -/
@[simp] theorem map_finiteAffineIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteAffineIdeal D) =
      N13CanonicalContractionQuotient.graphIdeal D := by
  simpa [finiteAffineIdeal] using
    N13IntegralModelContraction.map_contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Weighted reflection in the infinity variable converts a monic affine
equation into the same equation on the overlap, up to the invertible power
of `x = t⁻¹`. -/
theorem infinityReflect_mul_xPow_on_overlap
    (p : R₂[X]) :
    (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass
            (p.reflect p.natDegree)) *
        N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) := by
  letI : Invertible N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.invertible
  have hinv :
      ⅟N13OrdinaryCurveOverlap.xOverlap =
        N13OrdinaryCurveOverlap.tOverlap := by
    exact
      invOf_eq_right_inv
        (by simp [mul_comm])
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.xOverlap
      p.natDegree p le_rfl
  rw [hinv] at hreflect
  rw [show
      N13IntegralInfinityReduction.integralBaseClass
          (p.reflect p.natDegree) =
        N13IntegralInfinityGraphJacobian.xClassHom
          (p.reflect p.natDegree) by rfl,
    N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  simpa [N13OrdinaryCurveOverlap.affineCoeffMap] using hreflect
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A monic polynomial reflects at its degree to a polynomial with constant
coefficient one.  Separating that constant term exposes the infinity
uniformizer needed by the patching argument. -/
theorem reflect_natDegree_eq_one_add_X_mul
    (p : R₂[X]) (hp : p.Monic) :
    p.reflect p.natDegree =
      1 + X * (p.reflect p.natDegree).divX := by
  have hcoeff :
      (p.reflect p.natDegree).coeff 0 = 1 := by
    rw [Polynomial.coeff_reflect]
    simpa using hp.coeff_natDegree
  calc
    p.reflect p.natDegree =
        X * (p.reflect p.natDegree).divX +
          C ((p.reflect p.natDegree).coeff 0) :=
      (Polynomial.X_mul_divX_add _).symm
    _ = 1 + X * (p.reflect p.natDegree).divX := by
      rw [hcoeff, C_1]
      ring
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Finite affine support forces the infinity coordinate `t` to be a unit
modulo the contracted infinity closure.  A monic equation for `x` reflects
to a relation with constant coefficient one in `t`. -/
theorem infinityClosure_tUnitMod_of_finite
    (I : Ideal AffineCurve)
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    ∃ a : InfinityCurve,
      1 - N13IntegralInfinityChart.tClass * a ∈
        infinityClosure I := by
  letI : Module.Finite R₂ (AffineCurve ⧸ I) :=
    hfinite
  let xbar : AffineCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  obtain ⟨p, hpMonic, hpEval⟩ :=
    IsIntegral.of_finite R₂ xbar
  have hpMem :
      N13GeneralizedMumfordIntegral.xClassHom p ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass p) = 0
    rw [← N13ConcreteGraphRecovery.quotient_aeval_integralX]
    exact hpEval
  let r : R₂[X] :=
    p.reflect p.natDegree
  have hrMem :
      N13IntegralInfinityReduction.integralBaseClass r ∈
        infinityClosure I := by
    change
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass r) ∈
        Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I
    have hpMap :
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
            (N13GeneralizedMumfordIntegral.xClassHom p) ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I :=
      Ideal.mem_map_of_mem
        N13OrdinaryCurveOverlap.affineToInfinityOverlap hpMem
    have hprod :
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass r) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
      change
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass
                (p.reflect p.natDegree)) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I
      rw [infinityReflect_mul_xPow_on_overlap p]
      exact hpMap
    exact
      (Ideal.unit_mul_mem_iff_mem
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I)
        (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow
          p.natDegree)).mp
        (by simpa [mul_comm] using hprod)
  let q : InfinityCurve :=
    -N13IntegralInfinityReduction.integralBaseClass r.divX
  refine ⟨q, ?_⟩
  change
    N13IntegralInfinityReduction.integralBaseClass
        (p.reflect p.natDegree) ∈
      infinityClosure I at hrMem
  rw [reflect_natDegree_eq_one_add_X_mul p hpMonic] at hrMem
  convert hrMem using 1
  simp only [q, N13IntegralInfinityReduction.integralBaseClass,
    map_add, map_mul, map_one]
  rw [show
    (algebraMap
        N13IntegralInfinityReduction.IntegralBase
        N13IntegralInfinityReduction.IntegralRing) X =
      N13IntegralInfinityChart.tClass by rfl]
  rw [mul_neg, sub_neg_eq_add]
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine generic fibre of the finite quadratic proper line is exactly
the original Mumford graph ideal. -/
@[simp] theorem map_finiteQuadraticTwoChartLine_affineIdeal
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (AffineCurve ⧸ finiteAffineIdeal D)) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteQuadraticTwoChartLine D hdeg hfinite).affineIdeal =
      N13CanonicalContractionQuotient.graphIdeal D := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (finiteAffineIdeal D) =
      N13CanonicalContractionQuotient.graphIdeal D
  exact map_finiteAffineIdeal D
end
end MazurProof.N13FiniteAffineTwoChart
end
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
namespace MazurProof.N13QuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The proper line obtained from a finite quadratic graph is vertically
saturated on the affine chart.  Its affine ideal is definitionally the
canonical contraction of the generic Mumford graph. -/
theorem finiteQuadraticTwoChartLine_affineVerticallySaturated
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite N13FiniteAffineTwoChart.R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
        D.toSemi hdeg hfinite) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_contractIdeal
      _ (N13CanonicalContractionQuotient.graphIdeal D.toSemi)
  rfl
end
end MazurProof.N13QuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_of
    (f : Power) :
    evalBranchZero
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_of
    (f : Power) :
    evalBranchOne
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem positiveIntegralExpansion_t :
    positiveIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [positiveIntegralExpansion]
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem negativeIntegralExpansion_t :
    negativeIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [negativeIntegralExpansion]
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem map_top_of_t_unit_mod
    (f : B →+* P) (hf : f N13IntegralInfinityChart.tClass = PowerSeries.X)
    (I : Ideal B) (hI : ∃ a : B, 1 - N13IntegralInfinityChart.tClass * a ∈ I) :
    Ideal.map f I = ⊤ := by
  obtain ⟨a, ha⟩ := hI
  have hm : f (1 - N13IntegralInfinityChart.tClass * a) ∈ Ideal.map f I :=
    Ideal.mem_map_of_mem f ha
  have hu : IsUnit (f (1 - N13IntegralInfinityChart.tClass * a)) := by
    rw [map_sub, map_one, map_mul, hf, PowerSeries.isUnit_iff_constantCoeff]
    simpa using (isUnit_one : IsUnit (1 : N13FormalInfinityChart.R₂))
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left (Ideal.map f I) (↑(u⁻¹) : P) hm
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Finite affine support supplies an actual unit modulo the infinity
closure. Hence both generic formal infinity ideals are the unit ideal. -/
theorem finiteClosure_marked
    (I : Ideal N13FiniteAffineTwoChart.AffineCurve)
    (hI : IsUnit (I : N13FiniteAffineTwoChart.AffineFractionalIdeal))
    (hfinite : Module.Finite N13FiniteAffineTwoChart.R₂
      (N13FiniteAffineTwoChart.AffineCurve ⧸ I)) :
    HasInfinityMultiplicities
      (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite) 0 0 := by
  have ht := N13FiniteAffineTwoChart.infinityClosure_tUnitMod_of_finite I hfinite
  constructor
  · apply generic_map_of_integral positiveIntegralExpansion _ 0
    have h0 : Ideal.map positiveIntegralExpansion
        (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite).infinityIdeal = ⊤ :=
      map_top_of_t_unit_mod positiveIntegralExpansion positiveIntegralExpansion_t
        (N13FiniteAffineTwoChart.infinityClosure I) ht
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
  · apply generic_map_of_integral negativeIntegralExpansion _ 0
    have h0 : Ideal.map negativeIntegralExpansion
        (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite).infinityIdeal = ⊤ :=
      map_top_of_t_unit_mod negativeIntegralExpansion negativeIntegralExpansion_t
        (N13FiniteAffineTwoChart.infinityClosure I) ht
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
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
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem finiteQuadraticLine_marked
    (D : N13Mumford.SemiMumford N13TwoChartPicardRealization.Q₂)
    (hd : D.u.natDegree = 2)
    (hfinite : Module.Finite N13FiniteAffineTwoChart.R₂
      (N13FiniteAffineTwoChart.AffineCurve ⧸ N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    HasInfinityMultiplicities
      (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine D hd hfinite) 0 0 :=
  finiteClosure_marked _ _ _
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
theorem exists_saturated_data_of_finite
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite N13FiniteAffineTwoChart.R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  let L :=
    N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
      D.toSemi hdeg hfinite
  obtain ⟨Δ, hrestrict⟩ :=
    HuangN13.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
        D.toSemi hdeg hfinite
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
        SexticMumford.mumfordIdeal Model D.u D.v := by
    exact
      N13FiniteAffineTwoChart.map_finiteQuadraticTwoChartLine_affineIdeal
          D.toSemi hdeg hfinite
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
        (N13QuadraticPicardRealization.finiteQuadraticTwoChartLine_affineVerticallySaturated
          D hdeg hfinite)
  · exact finiteQuadraticLine_marked D.toSemi hdeg hfinite
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite MazurProof.N13FiniteAffineTwoChart.R₂
        (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸
          MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13MarkedQuadraticExistence.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.exists_saturated_data_of_finite D hdeg hfinite
