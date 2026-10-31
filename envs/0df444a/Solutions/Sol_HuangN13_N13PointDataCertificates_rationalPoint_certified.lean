-- Prove2me | solution 1 for HuangN13.N13PointDataCertificates.rationalPoint_certified
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:01:03.58361+00:00
-- url     : https://prove2.me/submissions/f44b075b-62f1-4a7e-833f-857f5d8c44f7

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_MazurProof_N13EscapingPointPicardRealization_affinePointIdeal_scalarSaturated
import Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_integralPointIdeal_quotient_finite
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_scalar_saturated
import Theorems.Thm_MazurProof_N13InfinityChartMarking_point_map_top_of_nonzero_t
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointIdeal_isUnit

set_option autoImplicit false

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
          _root_.Polynomial.C ((p.reflect p.natDegree).coeff 0) :=
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
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A line trivial on the affine chart is vertically saturated.  This covers
the degree-zero spread, whose divisor is supported entirely at infinity. -/
theorem affineVerticallySaturated_of_affineIdeal_eq_top
    (L : Line) (hL : L.affineIdeal = ⊤) :
    AffineVerticallySaturated L := by
  simp [AffineVerticallySaturated, hL]
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
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A line whose affine lattice is a monic generalized Mumford graph is
vertically saturated because its quotient is free over the coefficient
domain. -/
theorem affineVerticallySaturated_of_affineIdeal_eq_mumfordIdeal
    (L : Line)
    (D : N13GeneralizedMumfordIntegral.SemiMumford
      (R := N13IntegralModelContraction.R₂))
    (hL :
      L.affineIdeal =
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) :
    AffineVerticallySaturated L := by
  intro r hr a ha
  rw [hL] at ha ⊢
  change
    N13GeneralizedMumfordIntegral.xClass
          (Polynomial.C r) * a ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v at ha
  exact
    N13GeneralizedMumfordIntegral.scalar_saturated
      D r hr a ha
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The literal integral affine-point line is vertically saturated.  Its
affine lattice is a monic generalized Mumford graph, whose quotient has the
standard free coefficient basis. -/
theorem integralPointTwoChartLine_affineVerticallySaturated
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_mumfordIdeal
      _ (N13IntegralAffinePointSpread.integralSemiGraph P)
  rfl
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Adding the positive-infinity anchor preserves the affine lattice, so
the normalized degree-two integral-point line remains vertically saturated. -/
theorem anchoredPointLine_affineVerticallySaturated
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffinePointInfinityClosure.anchoredPointLine P) := by
  simpa [N13TwoChartPicardRealization.AffineVerticallySaturated,
    N13FiniteAffinePointInfinityClosure.anchoredPointLine] using
    integralPointTwoChartLine_affineVerticallySaturated P
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- The generic raw datum selected by `data` is the exact Mumford raw datum,
before passing to the quotient by principal oriented ideals. -/
theorem data_genericRaw_eq_mumfordRaw
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.genericRaw
        (data P).charts
        (data P).infinityOrder =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford P) := by
  change
    N13TwoChartPicardRealization.genericRaw
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P)
        (-1) =
      _
  exact genericRaw_anchoredPointLine_eq_mumfordRaw P
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The proper two-chart line of a nonintegral affine point is vertically
saturated on its ordinary affine chart. -/
theorem nonintegralPointLine_affineVerticallySaturated
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy) := by
  intro r hr a ha
  exact
    affinePointIdeal_scalarSaturated
      (N13ProperCurveReduction.nonintegralInfinityLift
        x y hx hxy)
      r hr a ha
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Adjoining the positive-infinity anchor changes only the infinity chart,
so the normalized escaping-point line retains affine vertical saturation. -/
theorem anchoredPointLine_affineVerticallySaturated
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13EscapingPointSpecialRestriction.anchoredPointLine
        x y hx hxy) := by
  simpa [N13TwoChartPicardRealization.AffineVerticallySaturated,
    N13EscapingPointSpecialRestriction.anchoredPointLine] using
      nonintegralPointLine_affineVerticallySaturated x y hx hxy
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The generic raw datum stored by `data` is the literal Mumford raw datum,
not merely the same class modulo principal oriented ideals. -/
theorem data_genericRaw_eq_mumfordRaw
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericRaw
        (data x y hx hxy).charts
        (data x y hx hxy).infinityOrder =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford x y hxy) := by
  change
    N13TwoChartPicardRealization.genericRaw
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      _
  exact
    genericRaw_anchoredPointLine_eq_mumfordRaw
      x y hx hxy
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The doubled positive-infinity line is vertically saturated on the
affine chart.  Both point factors are trivial there, so their tensor product
has the unit ideal and contains no vertical torsion. -/
theorem infinityPlusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityPlusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityPlusLine]
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The anchored negative-infinity line is vertically saturated on the
affine chart.  As for the positive branch, all geometric information lives
on the infinity chart and the affine ideal is the unit ideal. -/
theorem infinityMinusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityMinusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityMinusLine]
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_mem_xIdeal :
    branchZero ∈ xIdeal :=
  (Classical.choose_spec exists_branch_zero).2
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_constantCoeff :
    PowerSeries.constantCoeff branchZero = 0 := by
  have hle :
      xIdeal ≤ RingHom.ker
        (PowerSeries.constantCoeff : Power →+* R₂) := by
    rw [xIdeal, Ideal.span_le]
    intro z hz
    subst z
    exact RingHom.mem_ker.mpr PowerSeries.constantCoeff_X
  exact RingHom.mem_ker.mp (hle branchZero_mem_xIdeal)
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchOne_constantCoeff :
    PowerSeries.constantCoeff branchOne = -1 := by
  simp [branchOne, branchZero_constantCoeff,
    N13FormalInfinityChart.hPower]
end
end MazurProof.N13FormalInfinityBranches
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
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_vClass :
    evalBranchZero N13FormalInfinityChart.vClass =
      branchZero := by
  exact AdjoinRoot.lift_root eval₂_branchZero
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
@[simp] theorem evalBranchOne_vClass :
    evalBranchOne N13FormalInfinityChart.vClass =
      branchOne := by
  exact AdjoinRoot.lift_root eval₂_branchOne
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem hasInfinityMultiplicities_tensor
    (L M : Line) (p m q n : ℕ)
    (hL : HasInfinityMultiplicities L p m)
    (hM : HasInfinityMultiplicities M q n) :
    HasInfinityMultiplicities (N13TwoChartLineTensor.tensor L M) (p + q) (m + n) := by
  constructor
  · change Ideal.map positiveExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.1, hM.1, Ideal.span_singleton_mul_span_singleton, ← pow_add]
  · change Ideal.map negativeExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.2, hM.2, Ideal.span_singleton_mul_span_singleton, ← pow_add]
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem plus_ideal :
    N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass} : Set B) := by
  simp [N13TwoChartLineTensor.infinityPlusLine,
    N13TwoChartLineTensor.infinityPlusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem minus_ideal :
    N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass + 1} : Set B) := by
  simp [N13TwoChartLineTensor.infinityMinusLine,
    N13TwoChartLineTensor.infinityMinusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]
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
private theorem positiveIntegralExpansion_v :
    positiveIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchZero := by
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
private theorem negativeIntegralExpansion_v :
    negativeIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchOne := by
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
private theorem integral_plus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, positiveIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  exact PowerSeries.X_dvd_iff.mpr N13FormalInfinityBranches.branchZero_constantCoeff
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
private theorem integral_plus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal = ⊤ := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, negativeIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff, N13FormalInfinityBranches.branchOne_constantCoeff]
  exact isUnit_neg_one
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
private theorem integral_minus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal = ⊤ := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, map_add, map_one, positiveIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simpa [N13FormalInfinityBranches.branchZero_constantCoeff] using (isUnit_one : IsUnit (1 : N13FormalInfinityChart.R₂))
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
private theorem integral_minus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, map_add, map_one, negativeIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  apply PowerSeries.X_dvd_iff.mpr
  simp [N13FormalInfinityBranches.branchOne_constantCoeff]
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
theorem infinityPlusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityPlusLine 1 0 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_plus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_plus_on_minus)
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
theorem infinityMinusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityMinusLine 0 1 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_minus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_minus_on_minus)
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
theorem integralPointLine_marked
    (p : N13IntegralAffinePointSpread.IntegralPoint) :
    HasInfinityMultiplicities (N13FiniteAffineTwoChart.integralPointTwoChartLine p) 0 0 :=
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A point with nonzero generic t-coordinate is absent from both generic
infinity points even if it specializes onto one of them. -/
theorem infinityChartPointLine_marked
    (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) :
    HasInfinityMultiplicities (N13IntegralInfinityPointSpread.pointLine p) 0 0 := by
  constructor
  · have h0 : Ideal.map positiveExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      MazurProof.N13InfinityChartMarking.point_map_top_of_nonzero_t positiveExpansion positiveExpansion_base p hp
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
  · have h0 : Ideal.map negativeExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      MazurProof.N13InfinityChartMarking.point_map_top_of_nonzero_t negativeExpansion negativeExpansion_base p hp
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
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityPlus_certified : Certified N13InfinityPointPicardRealization.infinityPlusData := by
  refine ⟨(SexticMumford.zero Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityPlusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.zero]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityPlusLine_affineIdeal
  · have h := hasInfinityMultiplicities_tensor _ _ 1 0 1 0 infinityPlusLine_marked infinityPlusLine_marked
    convert h using 2 <;>
      first | rfl | simp [positiveMultiplicity, negativeMultiplicity, SexticMumford.zero]
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityMinus_certified : Certified N13InfinityPointPicardRealization.infinityMinusData := by
  refine ⟨(SexticMumford.infinityMinusMumford Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityMinusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.infinityMinusMumford]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityMinusLine_affineIdeal
  · have h := hasInfinityMultiplicities_tensor _ _ 0 1 1 0 infinityMinusLine_marked infinityPlusLine_marked
    convert h using 2 <;>
      first | rfl | simp [positiveMultiplicity, negativeMultiplicity, SexticMumford.infinityMinusMumford]
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem with_positive_anchor_marked (L : Line) (hL : HasInfinityMultiplicities L 0 0) :
    HasInfinityMultiplicities (N13TwoChartLineTensor.withPositiveInfinityMultiplicity L 1) 1 0 := by
  simpa [HasInfinityMultiplicities, N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartLineTensor.positiveInfinityPowerLine, N13TwoChartLineTensor.tensorPow,
    N13TwoChartLineTensor.tensor, N13TwoChartLineTensor.one] using
    hasInfinityMultiplicities_tensor L _ 0 0 1 0 hL infinityPlusLine_marked
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralPoint_certified (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Certified (N13IntegralPointPicardRealization.data P) := by
  let E := (N13IntegralPointPicardRealization.degreeOneMumford P).toSemi
  have hd : E.u.natDegree = 1 := by
    simp [E, N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
  have hn : E.nInf = 0 := rfl
  refine ⟨E, ?_, N13IntegralPointPicardRealization.data_genericRaw_eq_mumfordRaw P,
    N13IntegralPointPicardRealization.anchoredPointLine_affineVerticallySaturated P, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · change HasInfinityMultiplicities
      (N13TwoChartLineTensor.withPositiveInfinityMultiplicity
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P) 1)
      (positiveMultiplicity E) (negativeMultiplicity E)
    simpa [positiveMultiplicity, negativeMultiplicity, hd, hn] using
      with_positive_anchor_marked _ (integralPointLine_marked P)
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem escapingPoint_certified (x y : Q₂) (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Certified (N13EscapingPointPicardRealization.data x y hx hxy) := by
  let E := (N13EscapingPointPicardRealization.degreeOneMumford x y hxy).toSemi
  have hd : E.u.natDegree = 1 := by
    simp [E, N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
  have hn : E.nInf = 0 := rfl
  refine ⟨E, ?_, N13EscapingPointPicardRealization.data_genericRaw_eq_mumfordRaw x y hx hxy,
    N13EscapingPointPicardRealization.anchoredPointLine_affineVerticallySaturated x y hx hxy, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · have hm : HasInfinityMultiplicities
        (N13IntegralInfinityPointSpread.nonintegralPointLine x y hx hxy) 0 0 := by
      apply infinityChartPointLine_marked
      exact N13LocalDlogRegimes.inverseIntegralPart_ne_zero x hx
    change HasInfinityMultiplicities
      (N13TwoChartLineTensor.withPositiveInfinityMultiplicity
        (N13IntegralInfinityPointSpread.nonintegralPointLine x y hx hxy) 1)
      (positiveMultiplicity E) (negativeMultiplicity E)
    simpa [positiveMultiplicity, negativeMultiplicity, hd, hn] using with_positive_anchor_marked _ hm
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem rationalPoint_certified (P : N13RationalPointEndgame.RationalCurvePoint) :
    Certified (N13RationalCurvePointPicardRealization.data P).realization := by
  cases P with
  | infinityPlus => exact infinityPlus_certified
  | infinityMinus => exact infinityMinus_certified
  | affine X Y hcurve =>
    have hC13 : N13CurveModel.C13SexticEq X Y := by
      rw [N13CurveModel.C13SexticEq, ← N13Mumford.f_eval_eq_sexticF13]
      exact hcurve
    let x₂ : Q₂ := N13ProperCurveReduction.ratToQ₂ X
    let y₂ : Q₂ := N13ProperCurveReduction.ratToQ₂ (N13GoodModelTwo.sexticToGoodY X Y)
    have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
      N13ProperCurveReduction.map_good_equation hC13
    by_cases hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1
    · simp only [N13RationalCurvePointPicardRealization.data, dif_pos hx]
      change Certified (N13IntegralPointPicardRealization.data
        (N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood))
      exact integralPoint_certified _
    · simp only [N13RationalCurvePointPicardRealization.data, dif_neg hx]
      have hxval : x₂.valuation < 0 :=
        lt_of_not_ge ((Padic.norm_le_one_iff_val_nonneg x₂).not.mp hx)
      change Certified (N13EscapingPointPicardRealization.data x₂ y₂ hxval hgood)
      exact escapingPoint_certified x₂ y₂ hxval hgood
end
end MazurProof.N13PointDataCertificates
end
end


set_option autoImplicit false
open Polynomial
theorem solution (P : MazurProof.N13RationalPointEndgame.RationalCurvePoint) :
    MazurProof.N13EffectiveDataCompatibility.Certified (MazurProof.N13RationalCurvePointPicardRealization.data P).realization := by
  exact MazurProof.N13PointDataCertificates.rationalPoint_certified P
