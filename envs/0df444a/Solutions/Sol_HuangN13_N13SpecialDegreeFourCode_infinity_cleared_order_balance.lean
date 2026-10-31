-- Prove2me | solution 1 for HuangN13.N13SpecialDegreeFourCode.infinity_cleared_order_balance
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:33:33.199098+00:00
-- url     : https://prove2.me/submissions/8144afb3-11c1-4feb-997d-754c49df86c2

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_HuangN13_N13SpecialSmallNumerator_comparison_infinity_order_balance
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13SpecialAffineNorm_conjugate_linear
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityCoeffMap_hPoly
import Theorems.Thm_MazurProof_N13SpecialInfinityBranchJets_root_eval
import Theorems.Thm_MazurProof_N13SpecialLaurentBranches_root_relation

set_option autoImplicit false

namespace MazurProof.N13SpecialSmallNumerator
end MazurProof.N13SpecialSmallNumerator
section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
theorem infinityCurve_relation :
    N13SpecialInfinityChart.curvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13SpecialInfinityChart.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hPoly,
    infinityCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- Restriction of the infinity coordinate ring to the special affine
principal open. -/
def infinityToAffineOverlap :
    CoordinateRing →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13SpecialInfinityChart.curvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13SpecialInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13SpecialInfinityChart.tClass, infinityCoeffMap]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13SpecialInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13SpecialInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13SpecialInfinityChart.tClass
    infinity_tClass_mapsToUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : CoordinateRing) :
    infinityOverlapToAffineOverlap
        (algebraMap CoordinateRing InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13SpecialInfinityChart.tClass
      infinity_tClass_mapsToUnit z
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The reverse overlap map sends `t⁻¹` back to `x`. -/
@[simp] theorem infinityOverlapToAffineOverlap_xOverlap :
    infinityOverlapToAffineOverlap xOverlap = xAffineOverlap := by
  have hinv :
      tAffineOverlap *
          infinityOverlapToAffineOverlap xOverlap = 1 := by
    calc
      tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap =
          infinityOverlapToAffineOverlap tOverlap *
            infinityOverlapToAffineOverlap xOverlap := by
              rw [infinityOverlapToAffineOverlap_tOverlap]
      _ =
          infinityOverlapToAffineOverlap
            (tOverlap * xOverlap) := by
              rw [map_mul]
      _ = 1 := by rw [tOverlap_mul_xOverlap, map_one]
  calc
    infinityOverlapToAffineOverlap xOverlap =
        1 * infinityOverlapToAffineOverlap xOverlap := by simp
    _ =
        (xAffineOverlap * tAffineOverlap) *
          infinityOverlapToAffineOverlap xOverlap := by
            rw [xAffineOverlap_mul_tAffineOverlap]
    _ =
        xAffineOverlap *
          (tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap) := by
              rw [mul_assoc]
    _ = xAffineOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The forward overlap map sends `x⁻¹` back to `t`. -/
@[simp] theorem affineOverlapToInfinityOverlap_tAffineOverlap :
    affineOverlapToInfinityOverlap tAffineOverlap = tOverlap := by
  have hinv :
      xOverlap *
          affineOverlapToInfinityOverlap tAffineOverlap = 1 := by
    calc
      xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap =
          affineOverlapToInfinityOverlap xAffineOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap := by
              rw [affineOverlapToInfinityOverlap_xAffineOverlap]
      _ =
          affineOverlapToInfinityOverlap
            (xAffineOverlap * tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [xAffineOverlap_mul_tAffineOverlap, map_one]
  calc
    affineOverlapToInfinityOverlap tAffineOverlap =
        1 * affineOverlapToInfinityOverlap tAffineOverlap := by simp
    _ =
        (tOverlap * xOverlap) *
          affineOverlapToInfinityOverlap tAffineOverlap := by
            rw [tOverlap_mul_xOverlap]
    _ =
        tOverlap *
          (xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap) := by
              rw [mul_assoc]
    _ = tOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The reverse special overlap map is a left inverse of the forward map. -/
theorem infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap :
    infinityOverlapToAffineOverlap.comp
        affineOverlapToInfinityOverlap =
      RingHom.id AffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        infinityOverlapToAffineOverlap
            (affineOverlapToInfinityOverlap xAffineOverlap) =
          xAffineOverlap
      simp
  · change
      infinityOverlapToAffineOverlap
          (affineOverlapToInfinityOverlap yAffineOverlap) =
        yAffineOverlap
    simp
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The forward special overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13SpecialInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        affineOverlapToInfinityOverlap
            (infinityOverlapToAffineOverlap tOverlap) =
          tOverlap
      simp
  · change
      affineOverlapToInfinityOverlap
          (infinityOverlapToAffineOverlap vOverlap) =
        vOverlap
    simp
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The special principal opens of the affine and infinity charts agree. -/
noncomputable def overlapEquiv :
    AffineOverlap ≃+* InfinityOverlap where
  toEquiv :=
    { toFun := affineOverlapToInfinityOverlap
      invFun := infinityOverlapToAffineOverlap
      left_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap z
      right_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap z }
  map_mul' := affineOverlapToInfinityOverlap.map_mul
  map_add' := affineOverlapToInfinityOverlap.map_add
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem overlapEquiv_apply (z : AffineOverlap) :
    overlapEquiv z = affineOverlapToInfinityOverlap z :=
  rfl
end
end MazurProof.N13SpecialCurveOverlap
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem plus_base (p : K[X]) :
    plus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem minus_base (p : K[X]) :
    minus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem plus_v : plus N13SpecialInfinityChart.vClass = r₀ :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem minus_v : minus N13SpecialInfinityChart.vClass = r₁ :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem pointPolynomial_monic (P : CurvePoint) : (pointPolynomial P).Monic := by
  cases P
  · exact monic_X_sub_C _
  · exact monic_one
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem divisorPolynomial_monic (D : EffectiveDivisorTwo) : (divisorPolynomial D).Monic := by
  refine Sym2.inductionOn D ?_
  intro P Q
  exact (pointPolynomial_monic P).mul (pointPolynomial_monic Q)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem tensorPolynomial_monic (D E : EffectiveDivisorTwo) : (tensorPolynomial D E).Monic :=
  (divisorPolynomial_monic D).mul (divisorPolynomial_monic E)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_xClass (p : K[X]) : plus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_xClass (p : K[X]) : minus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_yClass : plus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_yClass : minus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem y_branch_sum : plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass =
    -base N13GoodCoordinateRingTwo.hPoly := by
  rw [plus_yClass, minus_yClass, N13SpecialInfinityBranchJets.r₁_eq, map_sub, map_neg]
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh]
  simp only [N13GoodCoordinateRingTwo.hPoly, map_add, map_pow, map_one, base_X]
  change t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ +
      t⁻¹ ^ 3 * (-(1 + t ^ 2 + t ^ 3) - includeSeries N13SpecialInfinityBranchJets.r₀) =
    -(t⁻¹ ^ 3 + t⁻¹ + 1)
  field_simp [t_ne_zero]
  ring
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem plus_conjugate (z : R) : plus (N13SpecialAffineNorm.conjugate z) = minus z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass,
    map_sub, map_neg]
  linear_combination -(base (N13GoodCoordinateRingTwo.coeffY z)) * y_branch_sum
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem branch_product (z : R) : plus z * minus z = base (N13SpecialAffineNorm.norm z) := by
  rw [← plus_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, plus_xClass]
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem plus_ne_zero (z : R) (hz : z ≠ 0) : plus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact left_ne_zero_of_mul hn
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem minus_ne_zero (z : R) (hz : z ≠ 0) : minus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact right_ne_zero_of_mul hn
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem branch_base (negative : Bool) (p : K[X]) :
    includeSeries (infinityBranch negative (algebraMap K[X] B p)) =
      p.eval₂ (algebraMap K L) t := by
  cases negative
  · change includeSeries (N13SpecialInfinityBranchJets.plus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.plus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
  · change includeSeries (N13SpecialInfinityBranchJets.minus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.minus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
private theorem t_isUnit (negative : Bool) :
    IsUnit ((includeSeries.comp (infinityBranch negative)) N13SpecialInfinityChart.tClass) := by
  change IsUnit (includeSeries (infinityBranch negative (algebraMap K[X] B X)))
  rw [branch_base]
  simpa using (isUnit_iff_ne_zero.mpr t_ne_zero : IsUnit t)
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def overlapBranch (negative : Bool) : O →+* L :=
  IsLocalization.Away.lift N13SpecialInfinityChart.tClass (t_isUnit negative)
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_infinity (negative : Bool) (b : B) :
    overlapBranch negative (algebraMap B O b) = includeSeries (infinityBranch negative b) :=
  DFunLike.congr_fun
    (IsLocalization.Away.lift_comp N13SpecialInfinityChart.tClass (t_isUnit negative)) b
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_t (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.tOverlap = t := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B X)) = _
  rw [overlapBranch_infinity, branch_base]
  simp
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_x (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.xOverlap = t⁻¹ := by
  have he := congrArg (overlapBranch negative) N13SpecialCurveOverlap.tOverlap_mul_xOverlap
  rw [map_mul, overlapBranch_t, map_one] at he
  apply mul_left_cancel₀ t_ne_zero
  rw [he, mul_inv_cancel₀ t_ne_zero]
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem overlapBranch_coefficient (negative : Bool) (a : K) :
    overlapBranch negative (N13SpecialCurveOverlap.coefficientToInfinityOverlap a) =
      algebraMap K L a := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B (_root_.Polynomial.C a))) = _
  rw [overlapBranch_infinity, branch_base]
  simp
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
private theorem base_X' : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem overlapBranch_affine_hom (negative : Bool) :
    (overlapBranch negative).comp N13SpecialCurveOverlap.affineToInfinityOverlap =
      affineBranch negative := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap
          (AdjoinRoot.of N13GoodCoordinateRingTwo.curvePoly (_root_.Polynomial.C a))) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass (_root_.Polynomial.C a))
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_of]
      simp only [N13SpecialCurveOverlap.affineCoeffMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [overlapBranch_coefficient]
      cases negative <;> simp [affineBranch, base, N13BranchNorm.evalPoly]
    · change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.xClass) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass X)
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_xClass, overlapBranch_x]
      cases negative
      · simp only [affineBranch, Bool.false_eq_true, if_false, plus_xClass, base_X']
      · simp only [affineBranch, if_true, minus_xClass, base_X']
  · change overlapBranch negative
      (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.yClass) =
      affineBranch negative N13GoodCoordinateRingTwo.yClass
    rw [N13SpecialCurveOverlap.affineToInfinityOverlap_yClass]
    change overlapBranch negative (N13SpecialCurveOverlap.xOverlap ^ 3 *
      algebraMap B O N13SpecialInfinityChart.vClass) = _
    rw [map_mul, map_pow, overlapBranch_x, overlapBranch_infinity]
    cases negative
    · simp only [affineBranch, infinityBranch, Bool.false_eq_true, if_false, plus_yClass,
        N13SpecialInfinityBranchJets.plus_v]
    · simp only [affineBranch, infinityBranch, if_true, minus_yClass,
        N13SpecialInfinityBranchJets.minus_v]
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_affine (negative : Bool) (a : R) :
    overlapBranch negative (N13SpecialCurveOverlap.affineToInfinityOverlap a) =
      affineBranch negative a := DFunLike.congr_fun (overlapBranch_affine_hom negative) a
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
theorem cross_relation (negative : Bool) (a b : R) (c d : B)
    (h : N13SpecialCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13SpecialCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    affineBranch negative a * includeSeries (infinityBranch negative d) =
      affineBranch negative b * includeSeries (infinityBranch negative c) := by
  simpa only [map_mul, overlapBranch_affine, overlapBranch_infinity] using
    congrArg (overlapBranch negative) h
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem affineBranch_injective (negative : Bool) : Function.Injective (affineBranch negative) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra h
  have hn : affineBranch negative (a - b) ≠ 0 := by
    cases negative
    · exact plus_ne_zero _ h
    · exact minus_ne_zero _ h
  apply hn
  simp only [map_sub, hab, sub_self]
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
private theorem localization_hom_injective
    {A S T : Type*} [CommRing A] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (f : S →+* T) (hf : Function.Injective (f.comp (algebraMap A S))) :
    Function.Injective f := by
  have hzero (z : S) (hz : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M z
    have hfa : f (algebraMap A S a) = 0 := by rw [← ha, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hf (by simpa using hfa)
    rw [ha0, map_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right (IsLocalization.map_units S s).ne_zero
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by simp [map_sub, hab]))
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem overlapBranch_injective (negative : Bool) : Function.Injective (overlapBranch negative) := by
  have hi : Function.Injective
      ((overlapBranch negative).comp N13SpecialCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13SpecialCurveOverlap.xClass)
    intro a b hab
    apply affineBranch_injective negative
    change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO a)) =
      overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO b)) at hab
    simpa only [N13SpecialCurveOverlap.overlapEquiv_apply,
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      overlapBranch_affine] using hab
  intro a b hab
  apply N13SpecialCurveOverlap.overlapEquiv.symm.injective
  apply hi
  change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm a)) =
    overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm b))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hab
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinity_t_ne_zero : N13SpecialInfinityChart.tClass ≠ 0 := by
  have hd : N13SpecialInfinityChart.curvePoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree N13SpecialInfinityChart.curvePoly_monic.ne_zero,
      N13SpecialInfinityChart.curvePoly_natDegree]
    norm_num
  change AdjoinRoot.of N13SpecialInfinityChart.curvePoly X ≠ 0
  simpa only [map_zero] using
    (AdjoinRoot.of.injective_of_degree_ne_zero hd).ne (Polynomial.X_ne_zero : (X : K[X]) ≠ 0)
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinityBranch_injective (negative : Bool) : Function.Injective (infinityBranch negative) := by
  intro a b hab
  apply IsLocalization.injective O
    (powers_le_nonZeroDivisors_of_noZeroDivisors infinity_t_ne_zero)
  apply overlapBranch_injective negative
  simpa only [overlapBranch_infinity] using congrArg includeSeries hab
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinityBranch_ne_zero (negative : Bool) (b : B) (hb : b ≠ 0) : infinityBranch negative b ≠ 0 := by
  simpa only [map_zero] using (infinityBranch_injective negative).ne hb
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
private theorem include_ne_zero (p : P) (hp : p ≠ 0) : includeSeries p ≠ 0 := by
  have hne := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).ne hp
  rw [map_zero] at hne
  exact hne
end
end MazurProof.N13SpecialDegreeFourCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDegreeFourCode
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding R
open N13SpecialDivisorBranchOrders N13SpecialSmallNumerator
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem infinity_cleared_order_balance
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (affineBranch negative z).order + (tensorOrder negative D E : ℤ) +
        (tensorPolynomial D E).natDegree = (tensorOrder negative F H : ℤ) := by
  have hnonzero (w : R) (hw : w ≠ 0) : affineBranch negative w ≠ 0 := by
    simpa only [map_zero] using (N13SpecialBranchFaithfulness.affineBranch_injective negative).ne hw
  have ha := hnonzero h.aNum h.aNum_ne
  have hb := hnonzero h.aDen h.aDen_ne
  have hc := include_ne_zero _ (N13SpecialBranchFaithfulness.infinityBranch_ne_zero negative _ h.iNum_ne)
  have hd := include_ne_zero _ (N13SpecialBranchFaithfulness.infinityBranch_ne_zero negative _ h.iDen_ne)
  have he := congrArg HahnSeries.order (cross_relation negative _ _ _ _ h.overlap_eq)
  rw [HahnSeries.order_mul ha hd, HahnSeries.order_mul hb hc] at he
  have hi := HuangN13.N13SpecialSmallNumerator.comparison_infinity_order_balance negative D E F H h
  have hn := congrArg (affineBranch negative) hcross
  have hbase (p : K[X]) : affineBranch negative (N13GoodCoordinateRingTwo.xClass p) = base p := by
    cases negative <;> simp [affineBranch]
  simp only [map_mul, hbase] at hn
  have hq := (tensorPolynomial_monic D E).ne_zero
  have ho := congrArg HahnSeries.order hn
  rw [HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hq),
    HahnSeries.order_mul hb (hnonzero z hz), N13BranchNorm.evalPoly_order K _ hq] at ho
  omega
end
end MazurProof.N13SpecialDegreeFourCode
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (negative : Bool) (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialOverlapBranches.affineBranch negative z).order + (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative D E : ℤ) +
        (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E).natDegree = (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative F H : ℤ) := by
  exact MazurProof.N13SpecialDegreeFourCode.infinity_cleared_order_balance negative D E F H h z hz hcross
