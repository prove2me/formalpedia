-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.ReciprocalGraphClosure.exists_saturated_data
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:56:08.450697+00:00
-- url     : https://prove2.me/submissions/433927f1-b26d-4b68-b41b-393ef0770448

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore
import Theorems.Thm_HuangN13_N13IntegralInfinityGraphSpecialRestriction_restrict_twoChartLine
import Theorems.Thm_HuangN13_N13ReciprocalGraphPicardRealization_horizontalGraph_saturated_and_marked

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem xClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    xClass u ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem ySubClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    ySubClass xClass yClass v ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- Multiplying the horizontal equation by a factor whose image is a unit
does not change the graph ideal. -/
theorem graphIdeal_mul_left_eq_of_isUnit
    (xClass : R[X] →+* A) (yClass : A)
    (c u v : R[X]) (hc : IsUnit (xClass c)) :
    graphIdeal xClass yClass (c * u) v =
      graphIdeal xClass yClass u v := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [map_mul]
      exact Ideal.mul_mem_left _
        (xClass c) (xClass_mem_graphIdeal xClass yClass u v)
    · exact ySubClass_mem_graphIdeal xClass yClass u v
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨d, hdc⟩ := isUnit_iff_exists_inv.mp hc
      have hdc' : d * xClass c = 1 := by
        simpa [mul_comm] using hdc
      have hcu :
          xClass (c * u) ∈
            graphIdeal xClass yClass (c * u) v :=
        xClass_mem_graphIdeal xClass yClass (c * u) v
      have hdcu :=
        Ideal.mul_mem_left
          (graphIdeal xClass yClass (c * u) v) d hcu
      rw [map_mul] at hdcu
      simpa [← mul_assoc, hdc'] using hdcu
    · exact ySubClass_mem_graphIdeal xClass yClass (c * u) v
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- Replacing the graph ordinate by a congruent polynomial modulo the
horizontal equation does not change the graph ideal. -/
theorem graphIdeal_eq_of_dvd_sub
    (xClass : R[X] →+* A) (yClass : A)
    (u v V : R[X]) (h : u ∣ V - v) :
    graphIdeal xClass yClass u V =
      graphIdeal xClass yClass u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u v
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u v := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u v)
      have heq :
          ySubClass xClass yClass V =
            ySubClass xClass yClass v - xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_graphIdeal xClass yClass u v) hmultiple
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u V
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u V := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u V)
      have heq :
          ySubClass xClass yClass v =
            ySubClass xClass yClass V + xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_graphIdeal xClass yClass u V) hmultiple
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fibre of the affine half of an infinity graph is its
coefficient-extended, completed-square sextic graph. -/
theorem map_affineIdeal
    (D : GraphData) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affineIdeal D) =
      SexticMumford.mumfordIdeal GenericModel
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineU D))
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV D))) := by
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    ← Ideal.map_map]
  change
    Ideal.map N13GoodSexticCoordinateEquiv.toSextic
        (Ideal.map N13TwoAdicCoordinateBaseChange.extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (affineU D) (affineV D))) = _
  rw [N13TwoAdicCoordinateBaseChange.map_mumfordIdeal,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]
end
end MazurProof.N13IntegralInfinityGraphTwoChart
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
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- If weighted reflection recovers a nonzero scalar multiple of a Mumford
horizontal equation and the reflected ordinate recovers its graph modulo
that equation, then the affine half has exactly the prescribed generic
graph ideal. -/
theorem map_affineIdeal_eq_mumfordIdeal
    (E : GraphData)
    (D : SexticMumford.SemiMumford GenericModel)
    (c : N13TwoAdicCoordinateBaseChange.Q₂)
    (hc : c ≠ 0)
    (hu :
      N13TwoAdicCoordinateBaseChange.mapPoly (affineU E) =
        C c * D.u)
    (hv :
      D.u ∣
        N13GoodSexticMumfordTransport.completedGraph
            (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)) -
          D.v) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affineIdeal E) =
      SexticMumford.mumfordIdeal GenericModel D.u D.v := by
  rw [map_affineIdeal, hu]
  have hunit :
      IsUnit
        (SexticMumford.xClass GenericModel (C c)) := by
    change
      IsUnit
        (algebraMap N13TwoAdicCoordinateBaseChange.Q₂
          (SexticMumford.CoordinateRing GenericModel) c)
    exact
      (isUnit_iff_ne_zero.mpr hc).map
        (algebraMap N13TwoAdicCoordinateBaseChange.Q₂
          (SexticMumford.CoordinateRing GenericModel))
  change
    GeneralizedGraphIdealCore.graphIdeal
        (SexticMumford.xClassHom GenericModel)
        (SexticMumford.yClass GenericModel)
        (C c * D.u)
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E))) =
      GeneralizedGraphIdealCore.graphIdeal
        (SexticMumford.xClassHom GenericModel)
        (SexticMumford.yClass GenericModel) D.u D.v
  rw [GeneralizedGraphIdealCore.graphIdeal_mul_left_eq_of_isUnit
      (SexticMumford.xClassHom GenericModel)
      (SexticMumford.yClass GenericModel)
      (C c) D.u
      (N13GoodSexticMumfordTransport.completedGraph
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)))
      hunit,
    GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
      (SexticMumford.xClassHom GenericModel)
      (SexticMumford.yClass GenericModel)
      D.u D.v
      (N13GoodSexticMumfordTransport.completedGraph
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineV E)))
      hv]
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
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

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem reflect_reciprocal_explicit
    (a b : Q₂) :
    (X ^ 2 + C a * X + C b : Q₂[X]).reflect 2 =
      1 + C a * X + C b * X ^ 2 := by
  rw [reflect_add, reflect_add]
  have hX2 :
      ((X : Q₂[X]) ^ 2).reflect 2 = 1 := by
    simpa using
      (reflect_monomial 2 2 (R := Q₂))
  have hCX :
      (C a * X : Q₂[X]).reflect 2 = C a * X := by
    simpa using
      (reflect_C_mul_X_pow (R := Q₂) 2 1 (c := a))
  rw [hX2, hCX, reflect_C]
end
end MazurProof.N13ReciprocalQuadraticReflection
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The weight-two reflection of the monic reciprocal is the original
quadratic multiplied by its inverse constant term. -/
theorem reflect_monic_reciprocal
    (u : Q₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2)
    (h0 : u.coeff 0 ≠ 0) :
    (X ^ 2 +
        C (u.coeff 1 / u.coeff 0) * X +
        C ((u.coeff 0)⁻¹) : Q₂[X]).reflect 2 =
      C ((u.coeff 0)⁻¹) * u := by
  rw [reflect_reciprocal_explicit,
    N13IrreducibleQuadraticChart.monic_quadratic_eq u hu hdeg]
  apply Polynomial.ext
  intro n
  simp only [coeff_add, coeff_one, coeff_C_mul_X,
    coeff_C_mul, coeff_X_pow, coeff_C]
  by_cases hn : n ≤ 2
  · interval_cases n
    · simp [h0]
    · simp [div_eq_mul_inv, mul_comm]
    · norm_num [coeff_X]
  · have hn2 : 2 < n := Nat.lt_of_not_ge hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2ne : n ≠ 2 := by omega
    rw [coeff_X_of_ne_one hn1]
    simp [hn0, hn2ne]
end
end MazurProof.N13ReciprocalQuadraticReflection
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- If the reciprocal monic equation has integral coefficients, then the
generic fibre of its affine weighted closure is a nonzero scalar multiple
of the original Mumford horizontal equation. -/
theorem mapPoly_reflect_integralReciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    N13TwoAdicCoordinateBaseChange.mapPoly
        ((integralReciprocal a b).reflect 2) =
      C ((D.u.coeff 0)⁻¹) * D.u := by
  have hmMap :
      N13TwoAdicCoordinateBaseChange.mapPoly
          (integralReciprocal a b) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹) := by
    simpa [integralReciprocal,
      N13TwoAdicCoordinateBaseChange.mapPoly,
      N13TwoAdicCoordinateBaseChange.coeffMap,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap] using hm
  change
    ((integralReciprocal a b).reflect 2).map
        N13TwoAdicCoordinateBaseChange.coeffMap =
      C ((D.u.coeff 0)⁻¹) * D.u
  rw [← Polynomial.reflect_map]
  change
    (N13TwoAdicCoordinateBaseChange.mapPoly
        (integralReciprocal a b)).reflect 2 =
      C ((D.u.coeff 0)⁻¹) * D.u
  rw [hmMap]
  exact
    reflect_monic_reciprocal
      D.u D.u_monic hdeg h0
end
end MazurProof.N13ReciprocalQuadraticReflection
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
    (hm : (X ^ 2 + C (a : N13TwoChartPicardRealization.Q₂) * X +
        C (b : N13TwoChartPicardRealization.Q₂)) =
      X ^ 2 + C (D.u.coeff 1 / D.u.coeff 0) * X + C ((D.u.coeff 0)⁻¹)) :
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
theorem ReciprocalGraphClosure.exists_saturated_data
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (E : N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
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
  have huMonic : E.data.u.Monic := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_monic
        a b
  have huDegree : E.data.u.natDegree = 2 := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
        a b
  let L :=
    N13IntegralInfinityGraphTwoChart.twoChartLine
      E.data (by omega) E.v_degree E.w_degree huMonic.ne_zero
  let Dbar :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E.data huMonic
  let hDbarDegree :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E.data huMonic huDegree
  let Δ :=
    N13SpecialInfinityGraphDivisor.graphDivisor
      Dbar hDbarDegree
  have hrestrict :
      N13TwoChartSpecialRestriction.restrict L =
        N13SpecialDivisorCharts.ofDivisor Δ := by
    simpa [L, Dbar, hDbarDegree, Δ] using
      (HuangN13.N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine
        E.data huMonic huDegree E.v_degree E.w_degree)
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
          (N13IntegralInfinityGraphTwoChart.affineIdeal E.data) =
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v
    apply
      N13IntegralInfinityGraphTwoChart.map_affineIdeal_eq_mumfordIdeal
        E.data D.toSemi ((D.u.coeff 0)⁻¹)
    · exact inv_ne_zero h0
    · change
        N13TwoAdicCoordinateBaseChange.mapPoly
            (E.data.u.reflect 2) =
          C ((D.u.coeff 0)⁻¹) * D.u
      rw [E.data_u]
      exact
        N13ReciprocalQuadraticReflection.mapPoly_reflect_integralReciprocal
          D hdeg h0 a b hm
    · exact E.generic_ordinate
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
        ((HuangN13.N13ReciprocalGraphPicardRealization.horizontalGraph_saturated_and_marked).1 E)
  · exact (HuangN13.N13ReciprocalGraphPicardRealization.horizontalGraph_saturated_and_marked).2 E.data (by omega) E.v_degree E.w_degree huMonic.ne_zero
      (by rw [E.data_u]; exact reciprocal_constant_nonzero D a b h0 hm)
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    {D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model}
    {a b : MazurProof.N13IrreducibleQuadraticSpread.R₂}
    (E : MazurProof.N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) :
        MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
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
  exact MazurProof.N13MarkedQuadraticExistence.ReciprocalGraphClosure.exists_saturated_data E hdeg h0 hm
