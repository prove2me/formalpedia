-- Prove2me | solution 1 for HuangN13.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:30:35.983923+00:00
-- url     : https://prove2.me/submissions/b66aaa1c-4071-4fa6-b206-25ccb86d2df0

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13RankTwoSemiGraphRecovery_exists_integral_semiGraph_of_basis
import Theorems.Thm_HuangN13_N13RankTwoVerticalGraphRecovery_exists_verticalGraph_of_basis
import Theorems.Thm_HuangN13_N13SpecialGraphDivisorCharts_ofDivisor_graphDivisor_affineIdeal
import Theorems.Thm_HuangN13_N13SpecialQuadraticGraphRegularity_map_mumfordIdeal_eq_graphDivisor_affineIdeal
import Theorems.Thm_MazurProof_N13ContractQuotientXYBasis_exists_contractQuotient_basis_oneX_or_oneY
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
end
end MazurProof.N13GoodCoordinateRingTwo
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
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- The product of the two raw graph functions is the negative substituted
curve equation. -/
theorem ySubClass_mul_conjugateV_raw
    (xClass : R[X] →+* A) (yClass : A) (h rhs v : R[X])
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass v *
        ySubClass xClass yClass (conjugateV h v) =
      -xClass (v ^ 2 + h * v - rhs) := by
  calc
    ySubClass xClass yClass v *
          ySubClass xClass yClass (conjugateV h v) =
        yClass ^ 2 + xClass h * yClass -
          (xClass v ^ 2 + xClass h * xClass v) := by
      simp only [ySubClass, conjugateV, map_neg, map_sub]
      ring
    _ = xClass rhs - xClass (v ^ 2 + h * v) := by
      rw [hy, map_add, map_mul, map_pow]
    _ = -xClass (v ^ 2 + h * v - rhs) := by
      rw [map_sub]
      ring
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
theorem ySubClass_mul_conjugate
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass D.v *
        ySubClass xClass yClass (conjugateV h D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass xClass yClass D.v *
          ySubClass xClass yClass (conjugateV h D.v) =
        -xClass (D.v ^ 2 + h * D.v - rhs) :=
      ySubClass_mul_conjugateV_raw xClass yClass h rhs D.v hy
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [map_mul]
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
/-- A generalized graph and its hyperelliptic conjugate multiply to `(u)`.
The only regularity input is the explicit Bézout identity for
`u`, `2v+h`, and `w`. -/
theorem graphIdeal_mul_conj
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs)
    (hbez :
      ∃ a b c : R[X],
        a * D.u + b * (2 * D.v + h) + c * D.w = 1) :
    graphIdeal xClass yClass D.u D.v *
        graphIdeal xClass yClass D.u (conjugateV h D.v) =
      Ideal.span ({xClass D.u} : Set A) := by
  let I := graphIdeal xClass yClass D.u D.v
  let J :=
    graphIdeal xClass yClass D.u (conjugateV h D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine
      ⟨p₀ * q₀ * xClass D.u +
          p₀ * qY *
            ySubClass xClass yClass (conjugateV h D.v) +
          pY * q₀ * ySubClass xClass yClass D.v -
          pY * qY * xClass D.w,
        ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination
      pY * qY *
        ySubClass_mul_conjugate xClass yClass h rhs D hy
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, habc⟩ := hbez
    have huI : xClass D.u ∈ I :=
      xClass_mem_graphIdeal xClass yClass D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hvI : ySubClass xClass yClass D.v ∈ I :=
      ySubClass_mem_graphIdeal xClass yClass D.u D.v
    have hvJ :
        ySubClass xClass yClass (conjugateV h D.v) ∈ J :=
      ySubClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass D.u * xClass (2 * D.v + h) ∈ I * J := by
      have hp :
          xClass D.u *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass xClass yClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [two_mul, ySubClass, conjugateV, map_neg, map_sub,
        map_add]
      ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass xClass yClass D.v *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate xClass yClass h rhs D hy] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b * (xClass D.u * xClass (2 * D.v + h)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b * (xClass D.u * xClass (2 * D.v + h)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + h) + c * D.w) := by
          simp only [two_mul, map_add, map_mul]
          ring
        _ = xClass D.u * 1 := by rw [habc, map_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum
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
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem point_affineIdeal
    (P : N13SpecialDivisorCharts.AffinePoint) :
    (N13SpecialDivisorCharts.point (Sum.inl P)).affineIdeal =
      N13SpecialDivisorCharts.affinePointIdeal P := by
  rw [N13SpecialDivisorCharts.point]
  split <;> rfl
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
/-- A root of the horizontal equation gives its literal graph point. -/
def graphRootPoint
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    N13SpecialDivisorCharts.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      N13SpecialGraphDivisor.curveEquationAtRoot D ha⟩
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The infinity chart contribution of one graph root is unit at `x = 0`
and is the literal point ideal at `t = 1` when `x = 1`. -/
theorem graphRootPoint_infinityIdeal
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).infinityIdeal =
      if a = 0 then ⊤ else
        N13SpecialDivisorCharts.infinityPointIdeal
          1 (D.v.eval a) := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [graphRootPoint]
  split <;> rfl
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The infinity chart ideal of a split root divisor is the product of the
point contributions selected by its two roots. -/
theorem ofDivisor_graphRoots_infinityIdeal
    (D : SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).infinityIdeal =
      rootInfinityIdeal D z := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (graphRootPoint D a
              (hz a (Sym2.mem_mk_left a b)))).infinityIdeal *
          (N13SpecialDivisorCharts.point
            (graphRootPoint D b
              (hz b (Sym2.mem_mk_right a b)))).infinityIdeal =
        rootInfinityIdeal D s(a, b)
      rw [graphRootPoint_infinityIdeal,
        graphRootPoint_infinityIdeal, rootInfinityIdeal_mk]
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
/-- The canonical infinity chart ideal of a quadratic special graph is the
explicit product attached to its chosen unordered root pair. -/
theorem ofDivisor_graphDivisor_infinityIdeal
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      rootInfinityIdeal D
        (N13SpecialGraphDivisor.rootPair D hdeg) := by
  unfold N13SpecialGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialGraphDivisor.rootPoint D hdeg)
          (N13SpecialGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialGraphDivisor.rootPair D hdeg)
          hz := by
    apply Sym2.ext
    intro P
    rw [Sym2.mem_pmap_iff, Sym2.mem_pmap_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [hpmap]
  exact
    ofDivisor_graphRoots_infinityIdeal D
      (N13SpecialGraphDivisor.rootPair D hdeg) hz
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine chart ideal of one sheet is its literal point graph ideal. -/
theorem verticalPoint_affineIdeal (a y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint a y)).affineIdeal =
      mumfordIdeal (X - C a) (C y) := by
  change
    (N13SpecialDivisorCharts.point
        (Sum.inl
          (⟨(a, y), _⟩ :
            N13SpecialDivisorCharts.AffinePoint))).affineIdeal =
      _
  rw [N13SpecialGraphDivisorCharts.point_affineIdeal]
  rfl
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine vertical derivative is one at every special affine point. -/
theorem hPoly_eval (a : K) :
    hPoly.eval a = 1 := by
  simp only [hPoly, eval_add, eval_pow, eval_X, eval_one]
  fin_cases a <;> decide
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- Both finite base coordinates are roots of the affine right-hand side. -/
theorem rhsPoly_eval (a : K) :
    rhsPoly.eval a = 0 := by
  simp only [rhsPoly, eval_add, eval_pow, eval_X]
  fin_cases a <;> decide
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The two affine sheet ideals multiply to the principal fibre ideal. -/
theorem verticalPointIdeal_mul :
    ∀ a : K,
      mumfordIdeal (X - C a) 0 *
          mumfordIdeal (X - C a) 1 =
        Ideal.span ({xClass (X - C a)} :
          Set CoordinateRing) := by
  intro a
  let p : K[X] := X - C a
  have hrhs : p ∣ -rhsPoly := by
    have hdiv :
        p ∣ -rhsPoly - C ((-rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, rhsPoly_eval a] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw : -rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D :
      GeneralizedGraphIdealCore.SemiGraph hPoly rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by
        simpa using hw }
  have hhdiv : p ∣ hPoly - C 1 := by
    simpa [p, hPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval (p := hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u + B * (2 * D.v + hPoly) + C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      mumfordIdeal p (conjugateV 0) =
        mumfordIdeal p 1 := by
    have heval :
        (conjugateV 0).eval a = 1 := by
      simp [conjugateV, hPoly_eval a]
    have hdiv :
        p ∣ conjugateV 0 - C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := conjugateV 0) (a := a))
    simpa [mumfordIdeal,
      GeneralizedGraphIdealCore.graphIdeal,
      ySubClass,
      GeneralizedGraphIdealCore.ySubClass] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1 (conjugateV 0) hdiv)
  rw [← hconj]
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV hPoly 0) =
      Ideal.span ({xClassHom p} : Set CoordinateRing)
  exact
    (GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass hPoly rhsPoly D
      yClass_relation hbez)
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine ideal of a finite canonical divisor is `(X-a)`. -/
theorem canonicalDivisor_affineIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).affineIdeal =
      Ideal.span ({xClass (X - C a)} :
        Set CoordinateRing) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).affineIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).affineIdeal =
      _
  rw [verticalPoint_affineIdeal, verticalPoint_affineIdeal]
  simpa using verticalPointIdeal_mul a
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The ordinate on the special infinity chart satisfies its generalized
quadratic equation. -/
theorem infinity_yClass_relation :
    N13SpecialInfinityChart.vClass ^ 2 +
        (algebraMap K[X]
          N13SpecialDivisorCharts.SpecialInfinity)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (algebraMap K[X]
        N13SpecialDivisorCharts.SpecialInfinity)
          N13SpecialInfinityChart.rhsPoly := by
  change
    N13SpecialInfinityChart.vClass ^ 2 +
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.rhsPoly
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13SpecialInfinityChart.curvePoly]
  ring
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- At any `F₂`-rational base coordinate `t = a`, the two infinity-chart
sheet ideals multiply to the principal fibre ideal `(t-a)`. -/
theorem infinityPointIdeal_mul (a : K) :
    N13SpecialDivisorCharts.infinityPointIdeal a 0 *
        N13SpecialDivisorCharts.infinityPointIdeal a 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X] N13SpecialDivisorCharts.SpecialInfinity
              (C a)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  let xClassHom :
      K[X] →+* N13SpecialDivisorCharts.SpecialInfinity :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let yClass : N13SpecialDivisorCharts.SpecialInfinity :=
    N13SpecialInfinityChart.vClass
  let p : K[X] := X - C a
  have hrhs : p ∣ -N13SpecialInfinityChart.rhsPoly := by
    have heval :
        (-N13SpecialInfinityChart.rhsPoly).eval a = 0 := by
      simp only [N13SpecialInfinityChart.rhsPoly, eval_neg,
        eval_add, eval_X, eval_pow]
      fin_cases a <;> decide
    have hdiv :
        p ∣ -N13SpecialInfinityChart.rhsPoly -
          C ((-N13SpecialInfinityChart.rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, heval] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw :
      -N13SpecialInfinityChart.rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D : GeneralizedGraphIdealCore.SemiGraph
      N13SpecialInfinityChart.hPoly
      N13SpecialInfinityChart.rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by simpa using hw }
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly, eval_add,
      eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u +
            B * (2 * D.v + N13SpecialInfinityChart.hPoly) +
            C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0) =
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 := by
    have heval :
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0).eval a = 1 := by
      simp [GeneralizedGraphIdealCore.conjugateV, hhEval]
    have hdiv :
        p ∣
          GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0 -
            C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := GeneralizedGraphIdealCore.conjugateV
            N13SpecialInfinityChart.hPoly 0)
          (a := a))
    exact
      GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0) hdiv
  have hproduct :=
    GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass
        N13SpecialInfinityChart.hPoly
        N13SpecialInfinityChart.rhsPoly
        D infinity_yClass_relation hbez
  rw [hconj] at hproduct
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 =
      Ideal.span ({xClassHom p} :
        Set N13SpecialDivisorCharts.SpecialInfinity) at hproduct
  have hX :
      xClassHom X = N13SpecialInfinityChart.tClass := rfl
  simpa [N13SpecialDivisorCharts.infinityPointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    xClassHom, yClass, p, hX] using hproduct
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- At `t = 1`, the two infinity-chart sheet ideals multiply to `(t-1)`. -/
theorem infinityPointIdeal_one_mul :
    N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
        N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X]
              N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) :=
  infinityPointIdeal_mul 1
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point above `x = 0` is absent from the infinity chart. -/
theorem verticalPoint_zero_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
      (verticalPoint 0 y)).infinityIdeal = ⊤ := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineZeroPoint]
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point above `x = 1` has its literal ideal at `t = 1`. -/
theorem verticalPoint_one_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint 1 y)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal 1 y := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineOnePoint]
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The infinity ideal of a finite canonical fibre is unit above `x = 0`
and the principal ideal `(t-1)` above `x = 1`. -/
theorem canonicalDivisor_infinityIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).infinityIdeal =
      if a = 0 then ⊤ else
        Ideal.span
          ({N13SpecialInfinityChart.tClass -
              algebraMap K[X]
                N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
            Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).infinityIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).infinityIdeal =
      _
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · rw [verticalPoint_zero_infinityIdeal,
      verticalPoint_zero_infinityIdeal]
    simp
  · rw [verticalPoint_one_infinityIdeal,
      verticalPoint_one_infinityIdeal]
    simp only [if_false, one_ne_zero]
    change
      N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
          N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
        _
    exact infinityPointIdeal_one_mul
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialConstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- A monic quadratic factor of `v²+v` is the full polynomial `v²+v`. -/
theorem monicQuadratic_eq_X_sq_add_X
    (m w : K[X])
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : X ^ 2 + X = m * w) :
    m = X ^ 2 + X := by
  have htargetMonic : (X ^ 2 + X : K[X]).Monic := by
    apply monic_X_pow_add
    rw [degree_X]
    norm_num
  have htargetDegree : (X ^ 2 + X : K[X]).natDegree = 2 := by
    compute_degree
    norm_num
  have hmDegree : m.IsMonicOfDegree 2 :=
    ⟨hdeg, hm⟩
  have hprodDegree : (m * w).IsMonicOfDegree (2 + 0) := by
    rw [← hcurve]
    exact ⟨by simpa using htargetDegree, htargetMonic⟩
  have hwDegree : w.IsMonicOfDegree 0 :=
    hmDegree.of_mul_left hprodDegree
  have hw : w = 1 :=
    eq_one_of_monic_natDegree_zero
      hwDegree.monic hwDegree.natDegree_eq
  rw [hw, mul_one] at hcurve
  exact hcurve.symm
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- At a constant special horizontal coordinate, the sheet polynomial is
`y²+y`. -/
theorem verticalCurve_C (a : K) :
    verticalCurve (C a) = X ^ 2 + X := by
  unfold verticalCurve
  have hh := N13SpecialVerticalDivisorCharts.hPoly_eval a
  have hr := N13SpecialVerticalDivisorCharts.rhsPoly_eval a
  simp [comp_C, hh, hr]
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- In the slope-zero branch, the vertical graph ideal is the principal
fibre ideal `(x-a)`. -/
theorem verticalIdeal_eq_span_of_slope_zero
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : verticalCurve (C a) = m * w) :
    verticalIdeal m a 0 =
      Ideal.span
        ({N13GoodCoordinateRingTwo.xClass (X - C a)} :
          Set Ring) := by
  have hmShape : m = X ^ 2 + X := by
    apply
      N13SpecialConstantInfinityVerticalGraph.monicQuadratic_eq_X_sq_add_X
        m w hm hdeg
    rw [← hcurve, verticalCurve_C]
  let p : K[X] := X - C a
  let J : Ideal Ring :=
    Ideal.span
      ({N13GoodCoordinateRingTwo.xClass p} : Set Ring)
  have hpJ :
      N13GoodCoordinateRingTwo.xClass p ∈ J :=
    Ideal.subset_span (by simp)
  have hhdiv :
      p ∣ N13GoodCoordinateRingTwo.hPoly - C 1 := by
    simpa [p, N13SpecialVerticalDivisorCharts.hPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13GoodCoordinateRingTwo.hPoly) (a := a))
  have hrhsdiv :
      p ∣ N13GoodCoordinateRingTwo.rhsPoly := by
    simpa [p, N13SpecialVerticalDivisorCharts.rhsPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13GoodCoordinateRingTwo.rhsPoly) (a := a))
  have hhJ :
      N13GoodCoordinateRingTwo.xClass
          (N13GoodCoordinateRingTwo.hPoly - C 1) ∈ J := by
    obtain ⟨q, hq⟩ := hhdiv
    rw [hq, N13GoodCoordinateRingTwo.xClass_mul]
    exact
      Ideal.mul_mem_right
        (N13GoodCoordinateRingTwo.xClass q) J hpJ
  have hrhsJ :
      N13GoodCoordinateRingTwo.xClass
          N13GoodCoordinateRingTwo.rhsPoly ∈ J := by
    obtain ⟨q, hq⟩ := hrhsdiv
    rw [hq, N13GoodCoordinateRingTwo.xClass_mul]
    exact
      Ideal.mul_mem_right
        (N13GoodCoordinateRingTwo.xClass q) J hpJ
  have hyyJ :
      N13GoodCoordinateRingTwo.yClass ^ 2 +
          N13GoodCoordinateRingTwo.yClass ∈ J := by
    have hdelta :=
      Ideal.mul_mem_right
        N13GoodCoordinateRingTwo.yClass J hhJ
    have hmem := Ideal.sub_mem J hrhsJ hdelta
    have hrel := N13GoodCoordinateRingTwo.yClass_relation
    convert hmem using 1
    simp only [N13GoodCoordinateRingTwo.xClass_sub]
    have hOne :
        N13GoodCoordinateRingTwo.xClass (C (1 : K)) = 1 := rfl
    rw [hOne]
    linear_combination hrel
  have hpClass :
      N13GoodCoordinateRingTwo.xClass p =
        N13GoodCoordinateRingTwo.xClass X -
          algebraMap K Ring a := by
    rw [show
      N13GoodCoordinateRingTwo.xClass p =
        N13GoodCoordinateRingTwo.xClass X -
          N13GoodCoordinateRingTwo.xClass (C a) by
      simp [p]]
    congr 1
  rw [verticalIdeal]
  simp only [Polynomial.aeval_C, map_zero, zero_mul, add_zero]
  rw [← hpClass]
  change
    Ideal.span
        ({aeval N13GoodCoordinateRingTwo.yClass m,
          N13GoodCoordinateRingTwo.xClass p} : Set Ring) =
      J
  rw [hmShape]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using hyyJ
    · exact hpJ
  · apply Ideal.span_mono
    simp
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Translating a slope-one vertical factorization gives the horizontal
special semigraph equation. -/
theorem translated_curve_eq
    (m w : K[X])
    (a : K)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    (X + C a) ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * (X + C a) -
          N13GoodCoordinateRingTwo.rhsPoly =
      translate a m * translate a w := by
  have h :=
    congrArg (fun p : K[X] => p.comp (X + C a)) hcurve
  simp only [verticalCurve, pow_comp, add_comp, mul_comp,
    sub_comp, X_comp] at h
  rw [comp_assoc, translateLinear_comp_translateLinear, comp_X,
    comp_assoc, translateLinear_comp_translateLinear, comp_X] at h
  simpa [translate] using h
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialQuadraticGraphRegularity.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The translated slope-one vertical graph is regular horizontal special
Mumford data. -/
def horizontalGraph
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := translate a m
  v := X + C a
  w := translate a w
  u_monic := hm.comp_X_add_C a
  curve_eq := translated_curve_eq m w a hcurve
  bezout :=
    N13SpecialQuadraticGraphRegularity.quadratic_graph_bezout
      (translate a m) (X + C a) (translate a w)
      (hm.comp_X_add_C a)
      (by
        change (m.comp (X + C a)).natDegree = 2
        rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg])
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The translated horizontal polynomial retains degree two. -/
theorem horizontalGraph_u_natDegree
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    (horizontalGraph m w a hm hdeg hcurve).u.natDegree = 2 := by
  change (m.comp (X + C a)).natDegree = 2
  rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg]
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Evaluating at the special class `x` is the canonical base-polynomial
map into the affine coordinate ring. -/
theorem xClass_eq_aeval_xClass (p : K[X]) :
    N13GoodCoordinateRingTwo.xClass p =
      aeval (N13GoodCoordinateRingTwo.xClass X) p := by
  let ψ : K[X] →ₐ[K] Ring :=
    IsScalarTower.toAlgHom K K[X] Ring
  have h :
      aeval (N13GoodCoordinateRingTwo.xClass X) = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact (DFunLike.congr_fun h p).symm
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The equations `x=a+y` and `y=x+a` define the same element of the
special affine coordinate ring. -/
theorem verticalLinear_eq_horizontalLinear (a : K) :
    N13GoodCoordinateRingTwo.xClass X -
        aeval N13GoodCoordinateRingTwo.yClass (C a + X) =
      N13GoodCoordinateRingTwo.yClass -
        N13GoodCoordinateRingTwo.xClass (X + C a) := by
  simp only [map_add, Polynomial.aeval_C, aeval_X,
    N13GoodCoordinateRingTwo.xClass_add]
  have hCa :
      N13GoodCoordinateRingTwo.xClass (C a) =
        algebraMap K Ring a :=
    (IsScalarTower.algebraMap_apply K K[X] Ring a).symm
  rw [hCa]
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have htwo : (2 : Ring) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap K Ring) htwoK
  linear_combination
    (N13GoodCoordinateRingTwo.xClass X -
      N13GoodCoordinateRingTwo.yClass) * htwo
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Modulo the common slope-one linear equation, evaluating `m` at `y` or
at `x+a` gives the same class. -/
theorem verticalPolynomial_sub_horizontalPolynomial_mem
    (m : K[X])
    (a : K) :
    aeval N13GoodCoordinateRingTwo.yClass m -
        N13GoodCoordinateRingTwo.xClass (translate a m) ∈
      Ideal.span
        ({N13GoodCoordinateRingTwo.yClass -
            N13GoodCoordinateRingTwo.xClass
              (X + C a)} : Set Ring) := by
  let s : Ring :=
    N13GoodCoordinateRingTwo.xClass (X + C a)
  obtain ⟨q, hq⟩ :=
    sub_dvd_eval_sub N13GoodCoordinateRingTwo.yClass s
      (m.map (algebraMap K Ring))
  have hdiff :
      aeval N13GoodCoordinateRingTwo.yClass m -
          aeval s m =
        (N13GoodCoordinateRingTwo.yClass - s) * q := by
    simpa [Polynomial.aeval_def] using hq
  have hs :
      N13GoodCoordinateRingTwo.xClass (translate a m) =
        aeval s m := by
    rw [xClass_eq_aeval_xClass, translate, aeval_comp]
    apply congrArg (fun z : Ring => aeval z m)
    simpa only [s] using
      (xClass_eq_aeval_xClass (X + C a)).symm
  change
    aeval N13GoodCoordinateRingTwo.yClass m -
        N13GoodCoordinateRingTwo.xClass (translate a m) ∈
      Ideal.span
        ({N13GoodCoordinateRingTwo.yClass - s} : Set Ring)
  rw [hs, hdiff]
  exact
    Ideal.mul_mem_right q _
      (Ideal.subset_span (by simp))
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialAffineVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT
/-- A slope-one vertical graph ideal is literally the translated horizontal
Mumford ideal. -/
theorem verticalIdeal_eq_mumfordIdeal_of_slope_one
    (m : K[X])
    (a : K) :
    verticalIdeal m a 1 =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (translate a m) (X + C a) := by
  let g : Ring :=
    N13GoodCoordinateRingTwo.yClass -
      N13GoodCoordinateRingTwo.xClass (X + C a)
  let mY : Ring :=
    aeval N13GoodCoordinateRingTwo.yClass m
  let mX : Ring :=
    N13GoodCoordinateRingTwo.xClass (translate a m)
  have hlinear := verticalLinear_eq_horizontalLinear a
  have hdiff :
      mY - mX ∈ Ideal.span ({g} : Set Ring) := by
    exact verticalPolynomial_sub_horizontalPolynomial_mem m a
  rw [verticalIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal,
    N13GoodCoordinateRingTwo.ySubClass]
  simp only [map_one, one_mul]
  change Ideal.span ({mY, _} : Set Ring) =
    Ideal.span ({mX, g} : Set Ring)
  rw [hlinear]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmX :
          mX ∈ Ideal.span ({mX, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mY - mX ∈ Ideal.span ({mX, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hadd :=
        Ideal.add_mem (Ideal.span ({mX, g} : Set Ring)) hdiff' hmX
      simpa [g] using hadd
    · exact Ideal.subset_span (by simp [g])
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmY :
          mY ∈ Ideal.span ({mY, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mY - mX ∈ Ideal.span ({mY, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hsub :=
        Ideal.sub_mem (Ideal.span ({mY, g} : Set Ring)) hmY hdiff'
      simpa [g] using hsub
    · exact Ideal.subset_span (by simp [g])
end
end MazurProof.N13SpecialAffineVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- The unit ideal trivially makes the infinity coordinate invertible in
the quotient. -/
theorem top_tUnitMod :
    TUnitMod (⊤ : Ideal InfinityCurve) := by
  exact ⟨0, by simp⟩
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- The property that `t` is invertible modulo an ideal is preserved by
ideal products. -/
theorem mul_tUnitMod
    {I J : Ideal InfinityCurve}
    (hI : TUnitMod I)
    (hJ : TUnitMod J) :
    TUnitMod (I * J) := by
  obtain ⟨q, hq⟩ := hI
  obtain ⟨r, hr⟩ := hJ
  refine
    ⟨q + r -
        N13SpecialInfinityChart.tClass * q * r, ?_⟩
  have hprod := Ideal.mul_mem_mul hq hr
  convert hprod using 1
  ring
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- Multiplication by `t` can be cancelled modulo an ideal in which `t`
is already a unit. -/
theorem mem_of_t_mul_mem
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I)
    {z : InfinityCurve}
    (hz : N13SpecialInfinityChart.tClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := ht
  have h₁ := Ideal.mul_mem_right z I hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1
  ring
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- Every power of `t` can be cancelled modulo a `t`-saturated ideal. -/
theorem mem_of_t_pow_mul_mem
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I)
    (n : ℕ)
    {z : InfinityCurve}
    (hz : N13SpecialInfinityChart.tClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_t_mul_mem ht
      convert hz using 1
      all_goals simp only [pow_succ]
      all_goals ring
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- Localizing a `t`-saturated infinity ideal and contracting returns the
original ideal. -/
theorem infinityOverlapContracted_of_tUnitMod
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I) :
    Ideal.comap
        (algebraMap InfinityCurve InfinityOverlap)
        (Ideal.map
          (algebraMap InfinityCurve InfinityOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap InfinityCurve InfinityOverlap z ∈
        Ideal.map
          (algebraMap InfinityCurve InfinityOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13SpecialInfinityChart.tClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_t_pow_mul_mem ht n hmz
  · exact Ideal.le_comap_map
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Reduction preserves an explicit inverse relation for the infinity
coordinate. -/
theorem map_reduceCoordinate_tUnitMod
    {I : Ideal N13FiniteAffineTwoChart.InfinityCurve}
    (ht :
      ∃ q : N13FiniteAffineTwoChart.InfinityCurve,
        1 - N13IntegralInfinityChart.tClass * q ∈ I) :
    TUnitMod
      (Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate I) := by
  obtain ⟨q, hq⟩ := ht
  refine
    ⟨N13IntegralInfinityReduction.reduceCoordinate q, ?_⟩
  have hmap :=
    Ideal.mem_map_of_mem
      N13IntegralInfinityReduction.reduceCoordinate hq
  simpa only [map_sub, map_one, map_mul,
    N13IntegralInfinityReduction.reduce_tClass] using hmap
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
/-- Compatible special chart pairs with the same affine ideal and
`t`-saturated infinity ideals are equal. -/
theorem chartPair_eq_of_affineIdeal_eq
    (L M : N13TwoChartSpecialRestriction.ChartPair)
    (hL : TUnitMod L.infinityIdeal)
    (hM : TUnitMod M.infinityIdeal)
    (haffine : L.affineIdeal = M.affineIdeal) :
    L = M := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact haffine
  · have hoverlap :
        Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            L.infinityIdeal =
          Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            M.infinityIdeal := by
      rw [← L.overlap_eq, ← M.overlap_eq, haffine]
    rw [← infinityOverlapContracted_of_tUnitMod hL,
      ← infinityOverlapContracted_of_tUnitMod hM, hoverlap]
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinitySaturation.instFactPrimeOfNatNat_fLT
/-- A finite special point contribution makes `t` invertible: a point at
`x=0` contributes the unit ideal, while a point at `x=1` contributes
`t=1`. -/
theorem rootInfinityFactor_tUnitMod
    (a z : N13SpecialDivisorCharts.K) :
    TUnitMod
      (if a = 0 then
        (⊤ : Ideal InfinityCurve)
      else
        N13SpecialDivisorCharts.infinityPointIdeal 1 z) := by
  by_cases ha : a = 0
  · simp only [ha, if_true]
    exact top_tUnitMod
  · simp only [ha, if_false]
    refine ⟨1, ?_⟩
    have hgen :
        N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K)) ∈
          N13SpecialDivisorCharts.infinityPointIdeal 1 z :=
      Ideal.subset_span (by simp)
    have hneg :=
      (N13SpecialDivisorCharts.infinityPointIdeal 1 z).neg_mem hgen
    convert hneg using 1
    simp
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The canonical infinity ideal of a quadratic affine special graph makes
`t` invertible modulo the ideal. -/
theorem graphDivisor_infinity_tUnitMod
    (D : N13GoodCoordinateRingTwo.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    TUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).infinityIdeal := by
  rw [
    N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal]
  let z := N13SpecialGraphDivisor.rootPair D hdeg
  change
    TUnitMod
      (N13SpecialGraphDivisorCharts.rootInfinityIdeal D z)
  induction z using Sym2.ind with
  | _ a b =>
      rw [N13SpecialGraphDivisorCharts.rootInfinityIdeal_mk]
      exact
        mul_tUnitMod
          (rootInfinityFactor_tUnitMod a (D.v.eval a))
          (rootInfinityFactor_tUnitMod b (D.v.eval b))
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinitySaturation
noncomputable section
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinitySaturation.instFactPrimeOfNatNat_fLT
/-- The canonical two-sheet divisor above a finite base coordinate makes
`t` invertible on the infinity chart: it is absent at `x=0` and satisfies
`t=1` at `x=1`. -/
theorem canonicalDivisor_infinity_tUnitMod
    (a : N13SpecialDivisorCharts.K) :
    TUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).infinityIdeal := by
  rw [N13SpecialVerticalDivisorCharts.canonicalDivisor_infinityIdeal]
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · simp only [if_true]
    exact top_tUnitMod
  · simp only [if_false, one_ne_zero]
    refine ⟨1, ?_⟩
    have hgen :
        N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K)) ∈
          Ideal.span
            ({N13SpecialInfinityChart.tClass -
                algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
                  (C (1 : N13SpecialDivisorCharts.K))} :
              Set InfinityCurve) :=
      Ideal.subset_span (by simp)
    have hneg :=
      (Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K))} :
          Set InfinityCurve)).neg_mem hgen
    convert hneg using 1
    simp
end
end MazurProof.N13SpecialInfinitySaturation
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Reduction commutes with evaluation at the integral affine ordinate
class `y`. -/
theorem reduce_aeval_integralY (p : R₂[X]) :
    N13GeneralizedMumfordReduction.reduceCoordinate
        (aeval N13ConcreteGraphRecovery.integralY p) =
      aeval N13GoodCoordinateRingTwo.yClass
        (N13GeneralizedMumfordReduction.reducePoly p) := by
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (aeval N13GeneralizedMumfordIntegral.yClass p) =
      aeval N13GoodCoordinateRingTwo.yClass
        (N13GeneralizedMumfordReduction.reducePoly p)
  have h :=
    Polynomial.map_aeval_eq_aeval_map
      (R := R₂)
      (S := IntegralRing)
      (T := K)
      (U := N13GeneralizedMumfordReduction.SpecialRing)
      (φ := N13GeneralizedMumfordReduction.reduceBase)
      (ψ := N13GeneralizedMumfordReduction.reduceCoordinate)
      (by
        ext r
        change
          N13GoodCoordinateRingTwo.xClass
              (C (N13GeneralizedMumfordReduction.reduceBase r)) =
            N13GeneralizedMumfordReduction.reduceCoordinate
              (N13GeneralizedMumfordIntegral.xClass (C r))
        rw [N13GeneralizedMumfordReduction.reduce_xClass]
        simp [N13GeneralizedMumfordReduction.reducePoly])
      p N13GeneralizedMumfordIntegral.yClass
  rw [N13GeneralizedMumfordReduction.reduce_yClass] at h
  simpa only [
    N13GeneralizedMumfordReduction.reducePoly_apply] using h
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Coefficient reduction commutes with the vertical substitution equation
on the affine chart. -/
theorem reduce_verticalCurve
    (s : R₂[X]) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13RankTwoVerticalGraphRecovery.verticalCurve s) =
      N13SpecialAffineVerticalGraph.verticalCurve
        (N13GeneralizedMumfordReduction.reducePoly s) := by
  rw [N13RankTwoVerticalGraphRecovery.verticalCurve,
    N13SpecialAffineVerticalGraph.verticalCurve]
  change
    (X ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly.comp s * X -
        N13GeneralizedMumfordIntegral.rhsPoly.comp s).map
          N13GeneralizedMumfordReduction.reduceBase =
      _
  simp only [Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_comp]
  rw [show
      N13GeneralizedMumfordIntegral.hPoly.map
          N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.hPoly from
      N13GeneralizedMumfordReduction.reduce_hPoly,
    show
      N13GeneralizedMumfordIntegral.rhsPoly.map
          N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.rhsPoly from
      N13GeneralizedMumfordReduction.reduce_rhsPoly]
  rfl
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The recovered integral vertical factorization reduces to the
corresponding special factorization. -/
theorem reduced_vertical_curve_eq
    (E : VerticalGraph) :
    N13SpecialAffineVerticalGraph.verticalCurve
          (C (N13GeneralizedMumfordReduction.reduceBase E.a) +
            C (N13GeneralizedMumfordReduction.reduceBase E.c) * X) =
      N13GeneralizedMumfordReduction.reducePoly E.m *
        N13GeneralizedMumfordReduction.reducePoly E.w := by
  have h :=
    congrArg
      N13GeneralizedMumfordReduction.reducePoly E.curve_eq
  rw [reduce_verticalCurve] at h
  simpa [N13RankTwoVerticalGraphRecovery.VerticalGraph.s,
    N13GeneralizedMumfordReduction.reducePoly] using h
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced vertical quadratic remains monic. -/
theorem reduced_vertical_m_monic
    (E : VerticalGraph) :
    (N13GeneralizedMumfordReduction.reducePoly E.m).Monic :=
  E.m_monic.map N13GeneralizedMumfordReduction.reduceBase
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- A monic recovered vertical quadratic retains degree two after
reduction. -/
theorem reduced_vertical_m_natDegree
    (E : VerticalGraph)
    (hdeg : E.m.natDegree = 2) :
    (N13GeneralizedMumfordReduction.reducePoly E.m).natDegree = 2 := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    E.m_monic.natDegree_map, hdeg]
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Reducing a recovered integral vertical ideal gives its literal special
vertical graph ideal. -/
theorem map_verticalIdeal
    (E : VerticalGraph) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate E.ideal =
      N13SpecialAffineVerticalGraph.verticalIdeal
        (N13GeneralizedMumfordReduction.reducePoly E.m)
        (N13GeneralizedMumfordReduction.reduceBase E.a)
        (N13GeneralizedMumfordReduction.reduceBase E.c) := by
  rw [N13RankTwoVerticalGraphRecovery.VerticalGraph.ideal,
    N13SpecialAffineVerticalGraph.verticalIdeal,
    Ideal.map_span, Set.image_pair]
  simp only [map_sub, reduce_aeval_integralY]
  congr 2
  simp [N13RankTwoVerticalGraphRecovery.VerticalGraph.s,
    N13GeneralizedMumfordReduction.reducePoly,
    N13CanonicalContractionQuotient.integralX]
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The reduced infinity closure of a finite affine ideal is
`t`-saturated. -/
theorem finiteLine_infinity_tUnitMod
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    N13SpecialInfinitySaturation.TUnitMod
      (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
          D hdeg hfinite)).infinityIdeal := by
  apply
    N13SpecialInfinitySaturation.map_reduceCoordinate_tUnitMod
  exact
    N13FiniteAffineTwoChart.infinityClosure_tUnitMod_of_finite
      (N13FiniteAffineTwoChart.finiteAffineIdeal D) hfinite
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13FiniteQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialAffineVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteQuadraticSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- A finite quadratic canonical contraction restricts to the complete
canonical chart pair of a literal effective degree-two special divisor. -/
theorem exists_specialDivisor_of_finiteQuadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
      N13TwoChartSpecialRestriction.restrict
          (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
            D hdeg hfinite) =
        N13SpecialDivisorCharts.ofDivisor Δ := by
  rcases
      N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
        D hdeg hfinite with hx | hy
  · obtain ⟨b, hb⟩ := hx
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13TwoFiberNoEscape.pairFamily
            1
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13CanonicalContractionQuotient.integralX) := by
      simpa [N13FiniteFlatBasisLift.oneX,
        N13TwoFiberNoEscape.pairFamily] using hb
    obtain ⟨E, hEdeg, hI⟩ :=
      HuangN13.N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
        D b hb'
    let Ebar :=
      N13SpecialQuadraticGraphRegularity.reduceSemiMumford E hEdeg
    let hEbarDeg :=
      N13SpecialQuadraticGraphRegularity.reduceSemiMumford_u_natDegree
        E hEdeg
    let Δ :=
      N13SpecialGraphDivisor.graphDivisor Ebar hEbarDeg
    refine ⟨Δ, ?_⟩
    apply
      N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
    · exact finiteLine_infinity_tUnitMod D hdeg hfinite
    · exact
        N13SpecialInfinitySaturation.graphDivisor_infinity_tUnitMod
          Ebar hEbarDeg
    · change
        Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
            (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
      rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI]
      exact
        HuangN13.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal
          E hEdeg
  · obtain ⟨b, hb⟩ := hy
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13FiniteFlatBasisLift.oneX
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13ConcreteGraphRecovery.integralY) := by
      simpa [N13ContractQuotientXYBasis.integralY,
        N13ConcreteGraphRecovery.integralY] using hb
    obtain ⟨E, hmDegree, hI⟩ :=
      HuangN13.N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
        D b hb'
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one
          (N13GeneralizedMumfordReduction.reduceBase E.c)
          (ZMod.pow_card
            (N13GeneralizedMumfordReduction.reduceBase E.c)) with hc | hc
    · let Δ :=
        N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl
            (N13GeneralizedMumfordReduction.reduceBase E.a))
      refine ⟨Δ, ?_⟩
      apply
        N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
      · exact finiteLine_infinity_tUnitMod D hdeg hfinite
      · exact
          N13SpecialInfinitySaturation.canonicalDivisor_infinity_tUnitMod
            (N13GeneralizedMumfordReduction.reduceBase E.a)
      · change
          Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
              (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
            (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
        rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI,
          map_verticalIdeal, hc,
          N13SpecialAffineVerticalGraph.verticalIdeal_eq_span_of_slope_zero
              (N13GeneralizedMumfordReduction.reducePoly E.m)
              (N13GeneralizedMumfordReduction.reducePoly E.w)
              (N13GeneralizedMumfordReduction.reduceBase E.a)
              (reduced_vertical_m_monic E)
              (reduced_vertical_m_natDegree E hmDegree)
              (by
                simpa [hc] using reduced_vertical_curve_eq E),
          N13SpecialVerticalDivisorCharts.canonicalDivisor_affineIdeal]
    · let mbar :=
        N13GeneralizedMumfordReduction.reducePoly E.m
      let wbar :=
        N13GeneralizedMumfordReduction.reducePoly E.w
      let abar :=
        N13GeneralizedMumfordReduction.reduceBase E.a
      let hcurve :
          N13SpecialAffineVerticalGraph.verticalCurve
              (C abar + X) =
            mbar * wbar := by
        simpa [mbar, wbar, abar, hc] using
          reduced_vertical_curve_eq E
      let Ebar :=
        N13SpecialAffineVerticalGraph.horizontalGraph
          mbar wbar abar (reduced_vertical_m_monic E)
            (reduced_vertical_m_natDegree E hmDegree) hcurve
      let hEbarDeg :=
        N13SpecialAffineVerticalGraph.horizontalGraph_u_natDegree
          mbar wbar abar (reduced_vertical_m_monic E)
            (reduced_vertical_m_natDegree E hmDegree) hcurve
      let Δ :=
        N13SpecialGraphDivisor.graphDivisor Ebar hEbarDeg
      refine ⟨Δ, ?_⟩
      apply
        N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
      · exact finiteLine_infinity_tUnitMod D hdeg hfinite
      · exact
          N13SpecialInfinitySaturation.graphDivisor_infinity_tUnitMod
            Ebar hEbarDeg
      · change
          Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
              (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
            (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
        rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI,
          map_verticalIdeal, hc,
          N13SpecialAffineVerticalGraph.verticalIdeal_eq_mumfordIdeal_of_slope_one,
          HuangN13.N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
        rfl
end
end MazurProof.N13FiniteQuadraticSpecialRestriction
end
end


set_option autoImplicit false
open Polynomial
open Module
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.SemiMumford MazurProof.N13FiniteQuadraticSpecialRestriction.Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite MazurProof.N13FiniteQuadraticSpecialRestriction.R₂
        (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸
          MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    ∃ Δ : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo,
      MazurProof.N13TwoChartSpecialRestriction.restrict
          (MazurProof.N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
            D hdeg hfinite) =
        MazurProof.N13SpecialDivisorCharts.ofDivisor Δ := by
  exact MazurProof.N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic D hdeg hfinite
