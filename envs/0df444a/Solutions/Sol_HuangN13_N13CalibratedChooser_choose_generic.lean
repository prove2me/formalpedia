-- Prove2me | solution 1 for HuangN13.N13CalibratedChooser.choose_generic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:01:07.288992+00:00
-- url     : https://prove2.me/submissions/e1eedb9e-3095-4eb6-9d68-1f264a30e1c6

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Theorems.Thm_HuangN13_N13EffectiveDataCompatibility_exists_certified_realization
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_f_sub_sqrtInfinity_sq

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-- Multiplying the first generator by a polynomial unit does not change a
Mumford ideal.  The divisibility formulation avoids choosing that unit. -/
theorem mumfordIdeal_eq_of_dvd_dvd
    (u u' v : K[X]) (huu' : u ∣ u') (hu'u : u' ∣ u) :
    mumfordIdeal M u v = mumfordIdeal M u' v := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := hu'u
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u' v)
    · exact ySubClass_mem_mumfordIdeal M u' v
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := huu'
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u v)
    · exact ySubClass_mem_mumfordIdeal M u v
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-- The ideal product at the heart of one Cantor reduction step.

The Bezout condition is exactly the one supplied by `mumford_bezout` for
the semireduced pair `(u,V)` when `w = (f-V²)/u`. -/
theorem mumfordIdeal_mul_cantor
    (u w V : K[X])
    (hcurve : M.f - V ^ 2 = u * w)
    (hbezout :
      ∃ a b c : K[X],
        a * u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M u V * mumfordIdeal M w V =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M u V
  let J := mumfordIdeal M w V
  let g := ySubClass M V
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hfactor :
          xClass M u * xClass M w =
            ySubClass M V * (yClass M + xClass M V) := by
        symm
        calc
          ySubClass M V * (yClass M + xClass M V) =
              xClass M (M.f - V ^ 2) := by
            simp only [ySubClass]
            calc
              (yClass M - xClass M V) *
                  (yClass M + xClass M V) =
                  yClass M ^ 2 - xClass M V ^ 2 := by ring
              _ = xClass M M.f - xClass M V ^ 2 := by
                rw [yClass_sq]
              _ = xClass M (M.f - V ^ 2) := by
                rw [xClass_sub, xClass_pow]
          _ = xClass M (u * w) := by rw [hcurve]
          _ = xClass M u * xClass M w := by rw [xClass_mul]
      rw [hfactor]
      exact Ideal.mul_mem_right (yClass M + xClass M V) _
        (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (xClass M u) (Ideal.subset_span (Set.mem_singleton _))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass M w) (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (ySubClass M V) (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := hbezout
    have huI : xClass M u ∈ I :=
      xClass_mem_mumfordIdeal M u V
    have hwJ : xClass M w ∈ J :=
      xClass_mem_mumfordIdeal M w V
    have hgI : g ∈ I :=
      ySubClass_mem_mumfordIdeal M u V
    have hgJ : g ∈ J :=
      ySubClass_mem_mumfordIdeal M w V
    have hug : xClass M u * g ∈ I * J :=
      Ideal.mul_mem_mul huI hgJ
    have hgw : g * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul hgI hwJ
    have hgg : g * g ∈ I * J :=
      Ideal.mul_mem_mul hgI hgJ
    have huw : xClass M u * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul huI hwJ
    have htwoVg : xClass M (2 * V) * g ∈ I * J := by
      have hdifference := Ideal.sub_mem (I * J) huw hgg
      convert hdifference using 1
      change
        xClass M (2 * V) * ySubClass M V =
          xClass M u * xClass M w -
            ySubClass M V * ySubClass M V
      have hxTwo :
          xClass M (2 : K[X]) = (2 : CoordinateRing M) := by
        exact map_natCast (xClassHom M) 2
      calc
        xClass M (2 * V) * ySubClass M V =
            xClass M (M.f - V ^ 2) -
              ySubClass M V ^ 2 := by
          simp only [ySubClass]
          rw [show xClass M (M.f - V ^ 2) =
            yClass M ^ 2 - xClass M V ^ 2 by
              rw [yClass_sq, xClass_sub, xClass_pow]]
          simp only [xClass_mul]
          rw [hxTwo]
          ring
        _ = xClass M (u * w) -
              ySubClass M V ^ 2 := by rw [hcurve]
        _ = xClass M u * xClass M w -
              ySubClass M V * ySubClass M V := by
          rw [xClass_mul, pow_two]
    have ha : xClass M a * (xClass M u * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M a) hug
    have hb : xClass M b * (xClass M (2 * V) * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M b) htwoVg
    have hc : xClass M c * (g * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M c) hgw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M u * g) +
            xClass M b * (xClass M (2 * V) * g) +
            xClass M c * (g * xClass M w) = g := by
      calc
        _ = xClass M
              (a * u + b * (2 * V) + c * w) * g := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = g := by rw [hbez, xClass_one, one_mul]
    rw [heq] at hsum
    exact hsum
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_tensor_affineIdeal
    (L M : TwoChartLine) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (tensor L M).affineIdeal =
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          M.affineIdeal := by
  rw [tensor_affineIdeal, Ideal.map_mul]
end
end MazurProof.N13TwoChartLineTensor
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
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem pointY_goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.pointY x (goodY x Y) = Y := by
  simp only [N13EscapingDegreeOneSpread.pointY, goodY]
  ring
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the integral point line is the standard
sextic point graph. -/
theorem map_integralPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  have hmap :=
    N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal P
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [hmap]
  simp [P,
    N13ProperCurveReduction.integralAffineLift,
    N13IntegralAffinePointSpread.curvePoint,
    N13IntegralAffinePointSpread.sexticY,
    N13EscapingDegreeOneSpread.pointY,
    SexticMumford.pointMumford,
    SexticMumford.affinePointMumford]
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the escaping point line is the same standard
sextic point graph. -/
theorem map_escapingPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (escapingPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
  exact
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint
      x y hx hcurve
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The valuation-independent point line always has the standard point graph
as its generic affine ideal. -/
theorem map_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pointLine x y hcurve).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
  rw [pointLine]
  split
  · exact map_integralPointLine_affineIdeal x y hcurve _
  · exact map_escapingPointLine_affineIdeal x y hcurve _
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the pair line is the product of the two
standard point graph ideals. -/
theorem map_pairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pairLine x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal Model
          (X - _root_.Polynomial.C x₁)
          (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal Model
          (X - _root_.Polynomial.C x₂)
          (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [pairLine, N13TwoChartLineTensor.map_tensor_affineIdeal,
    map_pointLine_affineIdeal, map_pointLine_affineIdeal]
end
end MazurProof.N13QuadraticTwoChartSpread
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
namespace MazurProof.N13Arithmetic
/-- Include an affine point in the projective point encoding. -/
def affine13 (X Y : ℚ) (h : N13CurveModel.C13SexticEq X Y) : Point13 :=
  Sum.inl ⟨(X, Y), h⟩
end MazurProof.N13Arithmetic
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
namespace MazurProof.N13Arithmetic
/-- Sextic point (-1,1); optimized point (0,0). -/
def A : Point13 :=
  affine13 (-1) 1
    (N13CurveModel.affine_cusp_mem (Or.inr rfl) (Or.inl rfl))
end MazurProof.N13Arithmetic
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
namespace MazurProof.N13Arithmetic
/-- Sextic point (0,1); optimized point (-1,0). -/
def C : Point13 :=
  affine13 0 1
    (N13CurveModel.affine_cusp_mem (Or.inl rfl) (Or.inl rfl))
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private def cM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint C)
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private def aM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint A)
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private def tM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint T)
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem cM13_u :
    cM13.u = (X : ℚ[X]) := by
  change X - Polynomial.C (0 : ℚ) = X
  simp
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem cM13_v :
    cM13.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem cM13_nInf :
    cM13.nInf = 0 := by
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem aM13_u :
    aM13.u = (X + 1 : ℚ[X]) := by
  change X - Polynomial.C (-1 : ℚ) = X + 1
  simp
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem aM13_v :
    aM13.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem aM13_nInf :
    aM13.nInf = 0 := by
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
@[simp] private theorem tM13_nInf :
    tM13.nInf = 0 := by
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem four_mul_quarter13 :
    (4 : ℚ[X]) * quarter13 = 1 := by
  change Polynomial.C (4 : ℚ) * Polynomial.C (1 / 4 : ℚ) = Polynomial.C (1 : ℚ)
  rw [← C_mul]
  norm_num
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem X_dvd_negs13_sub_one :
    (X : ℚ[X]) ∣ -s13 - (1 : ℚ[X]) := by
  refine ⟨-(X + 1) ^ 2, ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem X_add_one_dvd_negs13_sub_one :
    (X + 1 : ℚ[X]) ∣ -s13 - (1 : ℚ[X]) := by
  refine ⟨-(X * (X + 1)), ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem scaled_A_ideal :
    SexticMumford.mumfordIdeal M13
        (4 * (X + 1 : ℚ[X])) (-s13) =
      SexticMumford.mumfordIdeal M13
        (X + 1 : ℚ[X]) (-s13) := by
  apply SexticMumford.mumfordIdeal_eq_of_dvd_dvd
  · refine ⟨quarter13, ?_⟩
    calc
      (X + 1 : ℚ[X]) = 1 * (X + 1) := by ring
      _ = ((4 : ℚ[X]) * quarter13) * (X + 1) := by
        rw [four_mul_quarter13]
      _ = (4 * (X + 1)) * quarter13 := by ring
  · refine ⟨(4 : ℚ[X]), ?_⟩
    ring
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_curve_factor :
    M13.f - (-s13) ^ 2 =
      (X : ℚ[X]) * (4 * (X + 1 : ℚ[X])) := by
  rw [neg_sq, N13Mumford.model_f]
  rw [show s13 =
      (N13MumfordInfinityBalance.sqrtInfinity : ℚ[X]) from rfl,
    N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq]
  ring
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_bezout :
    ∃ a b c : ℚ[X],
      a * X + b * (2 * (-s13)) +
          c * (4 * (X + 1)) = 1 := by
  have hq :
      quarter13 * (4 : ℚ[X]) = 1 := by
    simpa [mul_comm] using four_mul_quarter13
  refine ⟨-1, 0, quarter13, ?_⟩
  calc
    (-1 : ℚ[X]) * X + 0 * (2 * (-s13)) +
          quarter13 * (4 * (X + 1)) =
        -X + (quarter13 * 4) * (X + 1) := by
          ring
    _ = -X + (X + 1) := by
      rw [hq, one_mul]
    _ = 1 := by ring
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_point_ideal_mul :
    SexticMumford.mumfordIdeal M13
          cM13.toSemi.u cM13.toSemi.v *
        SexticMumford.mumfordIdeal M13
          aM13.toSemi.u aM13.toSemi.v =
      Ideal.span
        ({SexticMumford.ySubClass M13 (-s13)} :
          Set (N13Mumford.CoordinateRing ℚ)) := by
  simp only [SexticMumford.toSemi_u, SexticMumford.toSemi_v,
    cM13_u, cM13_v, aM13_u, aM13_v]
  calc
    SexticMumford.mumfordIdeal M13 X 1 *
          SexticMumford.mumfordIdeal M13 (X + 1) 1 =
        SexticMumford.mumfordIdeal M13 X (-s13) *
          SexticMumford.mumfordIdeal M13 (X + 1) (-s13) := by
            rw [← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 X 1 (-s13) X_dvd_negs13_sub_one,
              ← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 (X + 1) 1 (-s13)
                    X_add_one_dvd_negs13_sub_one]
    _ =
        SexticMumford.mumfordIdeal M13 X (-s13) *
          SexticMumford.mumfordIdeal M13
            (4 * (X + 1)) (-s13) := by
              rw [scaled_A_ideal]
    _ =
        Ideal.span
          ({SexticMumford.ySubClass M13 (-s13)} :
            Set (N13Mumford.CoordinateRing ℚ)) := by
              exact SexticMumford.mumfordIdeal_mul_cantor
                M13
                (X : ℚ[X])
                (4 * (X + 1 : ℚ[X]))
                (-s13)
                ca_curve_factor
                ca_bezout
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem caFn13_finite_principal :
    SexticMumford.mumfordIdealUnit M13 cM13.toSemi *
        SexticMumford.mumfordIdealUnit M13 aM13.toSemi =
      toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) caFn13 := by
  apply Units.ext
  simp only [Units.val_mul,
    SexticMumford.coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, caFn13,
    SexticMumford.coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    ca_point_ideal_mul,
    FractionalIdeal.coeIdeal_span_singleton]
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem z13_deg :
    z13.u.natDegree ≤ 2 := by
  simp [z13]
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem minusLift_z13 :
    N13MumfordInfinityBalance.minusLift z13 = -s13 := by
  simp [z13, s13,
    N13MumfordInfinityBalance.minusLift,
    N13MumfordInfinityBalance.minusRemainder]
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_positive_order :
    (N13Infinity.coordinateToLaurent ℚ
      (SexticMumford.ySubClass M13 (-s13))).order = -3 := by
  have h :=
    N13MumfordInfinityBalance.minusYSub_plus_order
      z13 z13_deg
  rw [minusLift_z13] at h
  exact h
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem caFn13_ordPlus :
    Multiplicative.toAdd
        ((N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13) =
      -3 := by
  rw [caFn13,
    N13MumfordInfinityBalance.ordPlus_ySubFunctionUnit]
  exact ca_positive_order
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem tM13_idealUnit_one :
    SexticMumford.mumfordIdealUnit M13 tM13.toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal M13 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ)) = 1
  have hz := SexticMumford.zero_mumfordIdeal M13
  change SexticMumford.mumfordIdeal M13 1 0 = ⊤ at hz
  rw [hz]
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_mumfordRaw_relation :
    SexticMumford.mumfordRaw M13 cM13 *
        SexticMumford.mumfordRaw M13 aM13 *
          SexticMumford.mumfordRaw M13 tM13 =
      SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) caFn13 := by
  apply Prod.ext
  · change
      SexticMumford.mumfordIdealUnit M13 cM13.toSemi *
          SexticMumford.mumfordIdealUnit M13 aM13.toSemi *
            SexticMumford.mumfordIdealUnit M13 tM13.toSemi =
        toPrincipalIdeal
            (N13Mumford.CoordinateRing ℚ)
            (N13Mumford.FunctionField ℚ) caFn13
    rw [tM13_idealUnit_one, mul_one]
    exact caFn13_finite_principal
  · have hOrd :
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13 =
          Multiplicative.ofAdd (-3 : ℤ) := by
      simpa using
        congrArg Multiplicative.ofAdd caFn13_ordPlus
    change
      Multiplicative.ofAdd ((cM13.nInf : ℤ) - 1) *
          Multiplicative.ofAdd ((aM13.nInf : ℤ) - 1) *
            Multiplicative.ofAdd ((tM13.nInf : ℤ) - 1) =
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13
    rw [hOrd, cM13_nInf, aM13_nInf, tM13_nInf]
    change (-1 : ℤ) + (-1) + (-1) = -3
    norm_num
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private def raw13 (P : Point13) :
    SexticMumford.OrientedFrac M13 :=
  SexticMumford.mumfordRaw M13
    (SexticMumford.pointMumford M13
      (point13EquivCurvePoint P))
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_principal_mk_eq_one :
    QuotientGroup.mk' H13
        (SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) caFn13) =
      1 := by
  rw [QuotientGroup.mk'_apply]
  exact
    (QuotientGroup.eq_one_iff
      (SexticMumford.principalOriented M13
        (N13Infinity.positiveInfinityOrder ℚ) caFn13)).2
      (MonoidHom.mem_range.mpr ⟨caFn13, rfl⟩)
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ca_quotient_relation :
    QuotientGroup.mk' H13 (raw13 C) *
        QuotientGroup.mk' H13 (raw13 A) *
          QuotientGroup.mk' H13 (raw13 T) = (1 : Q13) := by
  have h : raw13 C * raw13 A * raw13 T =
      SexticMumford.principalOriented M13
        (N13Infinity.positiveInfinityOrder ℚ) caFn13 :=
    ca_mumfordRaw_relation
  rw [← map_mul, ← map_mul, h]
  exact ca_principal_mk_eq_one
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem AJ13_eq_raw (P : Point13) :
    AJ13 P =
      Additive.ofMul (QuotientGroup.mk' H13 (raw13 P)) := by
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
private theorem ofMul_add13 (a b : Q13) :
    (Additive.ofMul a : J13) + Additive.ofMul b =
      Additive.ofMul (a * b) := by
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- The cusp relation supplied by the principal divisor
    `div(Y+s) = C + A + T - 3O`, with `C = (0,1)`, `A = (-1,1)` the
    hyperelliptic conjugates of `D`, `B`. -/
theorem AJ13_C_add_A_add_T_eq_zero :
    AJ13 C + AJ13 A + AJ13 T = 0 := by
  rw [AJ13_eq_raw C, AJ13_eq_raw A, AJ13_eq_raw T,
    ofMul_add13, ofMul_add13, ca_quotient_relation]
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- Equivalently `AJ13 C + AJ13 A = -AJ13 T`: the class `O - T`
    (the degree-zero `nInf = 2` class relative to the anchor) is
    represented by `C + A - 2O`. -/
theorem AJ13_C_add_A_eq_neg_T :
    AJ13 C + AJ13 A = -AJ13 T :=
  eq_neg_of_add_eq_zero_left AJ13_C_add_A_add_T_eq_zero
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- The balanced representative `(1, 0, 2)`: the inverse of the
negative-infinity class (base point `∞₊`). -/
def oppositeInfinityMumford (K : Type*) [Field K] [CharZero K] :
    SexticMumford.Mumford (N13Mumford.model K) where
  u := 1
  v := 0
  nInf := 2
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
theorem oppositeInfinity_idealUnit_one (K : Type*) [Field K] [CharZero K] :
    SexticMumford.mumfordIdealUnit (N13Mumford.model K)
        (oppositeInfinityMumford K).toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing K)⁰
          (N13Mumford.FunctionField K)) = 1
  have hz := SexticMumford.zero_mumfordIdeal (N13Mumford.model K)
  change SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 = ⊤ at hz
  rw [hz]
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
theorem infinityMinus_idealUnit_one (K : Type*) [Field K] [CharZero K] :
    SexticMumford.mumfordIdealUnit (N13Mumford.model K)
        (SexticMumford.infinityMinusMumford (N13Mumford.model K)).toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing K)⁰
          (N13Mumford.FunctionField K)) = 1
  have hz := SexticMumford.zero_mumfordIdeal (N13Mumford.model K)
  change SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 = ⊤ at hz
  rw [hz]
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- `classOf (1,0,2) + classOf (1,0,0) = 0` over any field. -/
theorem classOf_opposite_add_infinityMinus (K : Type*) [Field K] [CharZero K] :
    SexticMumford.classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (oppositeInfinityMumford K) +
      SexticMumford.classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (SexticMumford.infinityMinusMumford (N13Mumford.model K)) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk' _
        (SexticMumford.mumfordRaw (N13Mumford.model K) (oppositeInfinityMumford K) *
          SexticMumford.mumfordRaw (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)))) = 0
  have hraw :
      SexticMumford.mumfordRaw (N13Mumford.model K) (oppositeInfinityMumford K) *
          SexticMumford.mumfordRaw (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)) = 1 := by
    apply Prod.ext
    · change
        SexticMumford.mumfordIdealUnit (N13Mumford.model K)
            (oppositeInfinityMumford K).toSemi *
          SexticMumford.mumfordIdealUnit (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)).toSemi = 1
      rw [oppositeInfinity_idealUnit_one, infinityMinus_idealUnit_one, mul_one]
    · change Multiplicative.ofAdd (((2 : ℕ) : ℤ) - 1) *
          Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1) = 1
      decide
  rw [hraw, map_one]
  rfl
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
theorem classOf_opposite_eq_neg_AJ13_T :
    SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) (oppositeInfinityMumford ℚ) =
      -AJ13 T := by
  have h := classOf_opposite_add_infinityMinus ℚ
  have hT : AJ13 T =
      SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ)
        (SexticMumford.infinityMinusMumford (N13Mumford.model ℚ)) := rfl
  rw [hT]
  exact eq_neg_of_add_eq_zero_left h
end MazurProof.N13Arithmetic
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
noncomputable section
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13Arithmetic
/-- The cusp pair `C + A` carries the nInf = 2 (opposite-infinity) class. -/
theorem AJ13_C_add_A_eq_classOf_opposite :
    AJ13 C + AJ13 A =
      SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) (oppositeInfinityMumford ℚ) := by
  rw [classOf_opposite_eq_neg_AJ13_T, AJ13_C_add_A_eq_neg_T]
end MazurProof.N13Arithmetic
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Base change of a rational balanced representative. -/
abbrev mapQ₂ (D : N13Mumford.Mumford ℚ) : N13Mumford.Mumford N13InfinityBaseChange.Q₂ :=
  D.mapCoeffs N13InfinityBaseChange.ratToQ₂ N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
abbrev cRat : N13Mumford.Mumford ℚ :=
  SexticMumford.pointMumford (N13Mumford.model ℚ) (point13EquivCurvePoint C)
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
abbrev aRat : N13Mumford.Mumford ℚ :=
  SexticMumford.pointMumford (N13Mumford.model ℚ) (point13EquivCurvePoint A)
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
theorem cRat_u : cRat.u = (X : ℚ[X]) := by
  change X - Polynomial.C (0 : ℚ) = X
  simp
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
theorem cRat_v : cRat.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
theorem aRat_u : aRat.u = (X + 1 : ℚ[X]) := by
  change X - Polynomial.C (-1 : ℚ) = X + 1
  simp
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
theorem aRat_v : aRat.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem genericIdealUnit_caLine :
    N13TwoChartPicardRealization.genericIdealUnit caLine =
      SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model (mapQ₂ cRat).toSemi *
        SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model (mapQ₂ aRat).toSemi := by
  apply Units.ext
  rw [Units.val_mul, N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit, SexticMumford.coe_mumfordIdealUnit,
    ← FractionalIdeal.coeIdeal_mul]
  congr 1
  have h := N13QuadraticTwoChartSpread.map_pairLine_affineIdeal
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1)
    MazurProof.N13InverseInfinityData.curve_zero MazurProof.N13InverseInfinityData.curve_negOne
  rw [N13TwoChartLineTensor.pointY_goodY, N13TwoChartLineTensor.pointY_goodY] at h
  refine h.trans ?_
  simp only [mapQ₂, SexticMumford.toSemi_u, SexticMumford.toSemi_v, SexticMumford.mapCoeffs_u,
    SexticMumford.mapCoeffs_v, cRat_u, cRat_v, aRat_u, aRat_v, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_add]
  simp
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem mapQ₂_oppositeInfinity :
    mapQ₂ (oppositeInfinityMumford ℚ) = oppositeInfinityMumford N13InfinityBaseChange.Q₂ := by
  have hu : (mapQ₂ (oppositeInfinityMumford ℚ)).u = (oppositeInfinityMumford N13InfinityBaseChange.Q₂).u := by
    simp [mapQ₂, oppositeInfinityMumford]
  have hv : (mapQ₂ (oppositeInfinityMumford ℚ)).v = (oppositeInfinityMumford N13InfinityBaseChange.Q₂).v := by
    simp [mapQ₂, oppositeInfinityMumford]
  have hn : (mapQ₂ (oppositeInfinityMumford ℚ)).nInf =
      (oppositeInfinityMumford N13InfinityBaseChange.Q₂).nInf := rfl
  generalize mapQ₂ (oppositeInfinityMumford ℚ) = D at hu hv hn
  cases D
  simp_all [oppositeInfinityMumford]
end MazurProof.N13InverseInfinityWitness
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- **The nInf = 2 witness realizes the opposite-infinity class.** -/
theorem inverseInfinityData_toGenericPic_eq_opposite :
    inverseInfinityData.toGenericPic =
      SexticMumford.classOf N13TwoChartPicardRealization.Model
        (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
        (oppositeInfinityMumford N13TwoChartPicardRealization.Q₂) := by
  have hraw :
      N13TwoChartPicardRealization.genericRaw caLine (-2) =
        SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model (mapQ₂ cRat) *
          SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model (mapQ₂ aRat) := by
    apply Prod.ext
    · exact genericIdealUnit_caLine
    · change Multiplicative.ofAdd (-2 : ℤ) =
        Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1) * Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1)
      decide
  have hsum :
      inverseInfinityData.toGenericPic =
        SexticMumford.classOf N13TwoChartPicardRealization.Model
            (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ cRat) +
          SexticMumford.classOf N13TwoChartPicardRealization.Model
            (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ aRat) := by
    change N13TwoChartPicardRealization.genericClass caLine (-2) = _
    unfold N13TwoChartPicardRealization.genericClass
    rw [hraw, map_mul]
    rfl
  have hC : SexticMumford.classOf N13TwoChartPicardRealization.Model
      (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ cRat) =
        N13InfinityBaseChange.picMapRatToQ₂ (AJ13 C) := by
    rw [show AJ13 C = SexticMumford.classOf (N13Mumford.model ℚ)
      (N13Infinity.positiveInfinityOrder ℚ) cRat from rfl, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  have hA : SexticMumford.classOf N13TwoChartPicardRealization.Model
      (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ aRat) =
        N13InfinityBaseChange.picMapRatToQ₂ (AJ13 A) := by
    rw [show AJ13 A = SexticMumford.classOf (N13Mumford.model ℚ)
      (N13Infinity.positiveInfinityOrder ℚ) aRat from rfl, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  rw [hsum, hC, hA, ← map_add, AJ13_C_add_A_eq_classOf_opposite,
    N13InfinityBaseChange.picMapRatToQ₂_classOf]
  exact congrArg _ mapQ₂_oppositeInfinity
end MazurProof.N13InverseInfinityWitness
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
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem chooseUncalibrated_generic (P : G) :
    (chooseUncalibrated P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P :=
  (Classical.choose_spec (HuangN13.N13EffectiveDataCompatibility.exists_certified_realization P)).2
end
end MazurProof.N13EffectiveDataCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
private theorem tClass_eq_classOf : tClass =
    SexticMumford.classOf (N13Mumford.model ℚ) (N13Infinity.positiveInfinityOrder ℚ)
      (SexticMumford.infinityMinusMumford (N13Mumford.model ℚ)) := rfl
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem infinityPlus_generic : N13InfinityPointPicardRealization.infinityPlusData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ (0 : G) := by
  rw [N13InfinityPointPicardRealization.infinityPlusData_toGenericPic,
    SexticMumford.classOf_zero, map_zero]
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
private theorem mumford_ext {D E : SexticMumford.Mumford Model}
    (hu : D.u = E.u) (hv : D.v = E.v) (hn : D.nInf = E.nInf) : D = E := by
  cases D
  cases E
  simp_all
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem infinityMinus_generic : N13InfinityPointPicardRealization.infinityMinusData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ tClass := by
  rw [N13InfinityPointPicardRealization.infinityMinusData_toGenericPic,
    tClass_eq_classOf, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  congr 1
  apply mumford_ext <;>
    simp [SexticMumford.infinityMinusMumford]
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem inverseInfinity_generic : N13InverseInfinityWitness.inverseInfinityData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ (-tClass) := by
  rw [N13InverseInfinityWitness.inverseInfinityData_toGenericPic_eq_opposite]
  have hm := N13InfinityBaseChange.picMapRatToQ₂_classOf (N13Arithmetic.oppositeInfinityMumford ℚ)
  rw [N13Arithmetic.classOf_opposite_eq_neg_AJ13_T] at hm
  rw [hm]
  exact congrArg (SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂))
    N13InverseInfinityWitness.mapQ₂_oppositeInfinity.symm
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem choose_generic (P : G) :
    (choose P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P := by
  unfold choose
  split
  · rename_i h; subst P; exact infinityPlus_generic
  · split
    · rename_i h; subst P; exact infinityMinus_generic
    · split
      · rename_i h; subst P; exact inverseInfinity_generic
      · exact chooseUncalibrated_generic P
end
end MazurProof.N13CalibratedChooser
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution (P : MazurProof.N13EffectiveDataCompatibility.G) :
    (MazurProof.N13CalibratedChooser.choose P).toGenericPic = MazurProof.N13InfinityBaseChange.picMapRatToQ₂ P := by
  exact MazurProof.N13CalibratedChooser.choose_generic P
