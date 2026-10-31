-- Prove2me | solution 1 for HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:21:03.341973+00:00
-- url     : https://prove2.me/submissions/4f163bbc-4b7d-4152-a643-d8e949bebdb1

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_MazurProof_N13EscapingPointPicardRealization_affinePointIdeal_scalarSaturated
import Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_integralPointIdeal_quotient_finite
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_scalar_saturated
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
import Theorems.Thm_MazurProof_N13QuadraticTwoChartSpreadSaturation_mul_scalar_saturated_of_left_isUnit

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
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
/-- Tensoring two vertically saturated two-chart lines preserves vertical
saturation on the affine chart.  Invertibility of the first affine ideal is
the essential hypothesis supplied by the line structure. -/
theorem affineVerticallySaturated_tensor
    (L M : N13TwoChartPicardRealization.Line)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L)
    (hM : N13TwoChartPicardRealization.AffineVerticallySaturated M) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor L M) := by
  change
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ L.affineIdeal * M.affineIdeal →
        a ∈ L.affineIdeal * M.affineIdeal
  exact
    mul_scalar_saturated_of_left_isUnit
      L.affineIdeal M.affineIdeal L.affine_isUnit hL hM
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Every valuation-independent point line is vertically saturated on the
ordinary affine chart. -/
theorem pointLine_affineVerticallySaturated
    (x y : N13QuadraticTwoChartSpread.Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13QuadraticTwoChartSpread.pointLine x y hcurve) := by
  rw [N13QuadraticTwoChartSpread.pointLine]
  split
  · let P : N13IntegralAffinePointSpread.IntegralPoint :=
      N13ProperCurveReduction.integralAffineLift x y ‹‖x‖ ≤ 1› hcurve
    change
      N13TwoChartPicardRealization.AffineVerticallySaturated
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)
    exact
      N13IntegralPointPicardRealization.integralPointTwoChartLine_affineVerticallySaturated P
  · exact
      N13EscapingPointPicardRealization.nonintegralPointLine_affineVerticallySaturated
        x y _ hcurve
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Tensoring the proper lines of two affine points preserves vertical
saturation.  This covers both split secants and repeated-root tangents. -/
theorem pairLine_affineVerticallySaturated
    (x₁ y₁ x₂ y₂ : N13QuadraticTwoChartSpread.Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂) := by
  change
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor
        (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)
        (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂))
  exact
    affineVerticallySaturated_tensor _ _
      (pointLine_affineVerticallySaturated x₁ y₁ hcurve₁)
      (pointLine_affineVerticallySaturated x₂ y₂ hcurve₂)
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
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
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem coeffMap_injective :
    Function.Injective coeffMap :=
  IsFractionRing.injective R₂ Q₂
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
private theorem point_map_top_of_nonzero_t
    (f : B →+* QP)
    (hf : ∀ p : N13IntegralInfinityChart.Base,
      f (N13IntegralInfinityPointSpread.xClassHom p) =
        N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p))
    (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) :
    Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p) = ⊤ := by
  have hm : f (N13IntegralInfinityPointSpread.xClassHom
      (N13IntegralInfinityPointSpread.pointU p)) ∈
      Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p) := by
    apply Ideal.mem_map_of_mem
    exact GeneralizedGraphIdealCore.xClass_mem_graphIdeal _ _ _ _
  have hc : PowerSeries.constantCoeff
      (f (N13IntegralInfinityPointSpread.xClassHom
        (N13IntegralInfinityPointSpread.pointU p))) =
      -N13TwoAdicInfinityCompatibility.coeffMap p.1.1 := by
    rw [hf]
    simp [N13IntegralInfinityPointSpread.pointU, N13IntegralInfinityChart.baseToPower,
      N13TwoAdicInfinityCompatibility.powerMap]
  have hn : N13TwoAdicInfinityCompatibility.coeffMap p.1.1 ≠ 0 := by
    intro hz
    apply hp
    apply N13TwoAdicInfinityCompatibility.coeffMap_injective
    simpa using hz
  have hu : IsUnit (f (N13IntegralInfinityPointSpread.xClassHom
      (N13IntegralInfinityPointSpread.pointU p))) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hn)
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left
    (Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p)) (↑(u⁻¹) : QP) hm
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A point with nonzero generic t-coordinate is absent from both generic
infinity points even if it specializes onto one of them. -/
theorem infinityChartPointLine_marked
    (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) :
    HasInfinityMultiplicities (N13IntegralInfinityPointSpread.pointLine p) 0 0 := by
  constructor
  · have h0 : Ideal.map positiveExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      point_map_top_of_nonzero_t positiveExpansion positiveExpansion_base p hp
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
  · have h0 : Ideal.map negativeExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      point_map_top_of_nonzero_t negativeExpansion negativeExpansion_base p hp
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
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem affinePointLine_marked
    (x y : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) :
    HasInfinityMultiplicities (N13QuadraticTwoChartSpread.pointLine x y h) 0 0 := by
  rw [N13QuadraticTwoChartSpread.pointLine]
  split
  · exact integralPointLine_marked _
  · apply infinityChartPointLine_marked
    rename_i hnorm
    exact N13LocalDlogRegimes.inverseIntegralPart_ne_zero x
      (lt_of_not_ge fun h0 => hnorm ((Padic.norm_le_one_iff_val_nonneg x).mpr h0))
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
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem pairLine_marked
    (x y z w : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y)
    (k : N13GoodModelTwo.AffineEquation z w) :
    HasInfinityMultiplicities (N13QuadraticTwoChartSpread.pairLine x y z w h k) 0 0 :=
  hasInfinityMultiplicities_tensor _ _ 0 0 0 0
    (affinePointLine_marked x y h) (affinePointLine_marked z w k)
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


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem solution :
    (∀
    (x₁ y₁ x₂ y₂ : MazurProof.N13QuadraticTwoChartSpread.Q₂)
    (hcurve₁ : MazurProof.N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : MazurProof.N13GoodModelTwo.AffineEquation x₂ y₂),
MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)) ∧
    (∀
    (x y z w : MazurProof.N13TwoChartPicardRealization.Q₂)
    (h : MazurProof.N13GoodModelTwo.AffineEquation x y)
    (k : MazurProof.N13GoodModelTwo.AffineEquation z w),
MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities (MazurProof.N13QuadraticTwoChartSpread.pairLine x y z w h k) 0 0) := by
  exact ⟨MazurProof.N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated, MazurProof.N13InfinityChartMarking.pairLine_marked⟩
