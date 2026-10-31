-- Prove2me | solution 1 for HuangN13.N13KernelInfinityMultiplicity.chosen_translated_finite_graph
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:09.442023+00:00
-- url     : https://prove2.me/submissions/b0ebd872-30e0-40cb-bca4-57550107d817

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13CalibratedChooser_choose_certified
import Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_point_specialClass
import Theorems.Thm_MazurProof_N13ProperCurveReduction_reduceCurve_cusp
import Theorems.Thm_MazurProof_N13SpecialInfinityBranchJets_root_eval

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem positiveMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (positiveMultiplicity E : ℤ) = E.nInf + 1 := by
  apply Int.toNat_of_nonneg
  have := h.2.1
  omega
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem negativeMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (negativeMultiplicity E : ℤ) = 1 - (E.u.natDegree : ℤ) - E.nInf := by
  apply Int.toNat_of_nonneg
  have := h.2.2
  omega
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num
end
end MazurProof.N13IntegralInfinityChart
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_curve_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
private theorem special_curve_degree :
    N13SpecialInfinityChart.curvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13SpecialInfinityChart.curvePoly_monic.ne_zero,
    N13SpecialInfinityChart.curvePoly_natDegree]
  norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem integralNormalPoly_eq (z : IntegralRing) :
    integralNormalPoly z =
      _root_.Polynomial.C (integralCoeff0 z) + _root_.Polynomial.C (integralCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13IntegralInfinityChart.infinityCurvePoly =
        _root_.Polynomial.C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0) +
          _root_.Polynomial.C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13IntegralInfinityChart.infinityCurvePoly)
        N13IntegralInfinityChart.infinityCurvePoly_monic
        (n := 2) (by rw [integral_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
theorem specialNormalPoly_eq (z : SpecialRing) :
    specialNormalPoly z =
      _root_.Polynomial.C (specialCoeff0 z) + _root_.Polynomial.C (specialCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13SpecialInfinityChart.curvePoly =
        _root_.Polynomial.C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 0) +
          _root_.Polynomial.C ((g %ₘ N13SpecialInfinityChart.curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.curvePoly_monic
        (n := 2) (by rw [special_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Every ordinary element has a unique rank-two expression. -/
theorem integral_recompose (z : IntegralRing) :
    integralBaseClass (integralCoeff0 z) +
        integralBaseClass (integralCoeffV z) *
          N13IntegralInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        integralBaseClass (integralCoeff0 (AdjoinRoot.mk _ g)) +
              integralBaseClass (integralCoeffV (AdjoinRoot.mk _ g)) *
                N13IntegralInfinityChart.vClass =
            AdjoinRoot.mk _
              (_root_.Polynomial.C (integralCoeff0 (AdjoinRoot.mk _ g)) +
                _root_.Polynomial.C (integralCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [integralBaseClass,
                    N13IntegralInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (integralNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [integralNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13IntegralInfinityChart.infinityCurvePoly_monic
            (AdjoinRoot.mk _ g)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Every special element has a unique rank-two expression. -/
theorem special_recompose (z : SpecialRing) :
    specialBaseClass (specialCoeff0 z) +
        specialBaseClass (specialCoeffV z) *
          N13SpecialInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        specialBaseClass (specialCoeff0 (AdjoinRoot.mk _ g)) +
              specialBaseClass (specialCoeffV (AdjoinRoot.mk _ g)) *
                N13SpecialInfinityChart.vClass =
            AdjoinRoot.mk _
              (_root_.Polynomial.C (specialCoeff0 (AdjoinRoot.mk _ g)) +
                _root_.Polynomial.C (specialCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [specialBaseClass,
                    N13SpecialInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (specialNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [specialNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13SpecialInfinityChart.curvePoly_monic
            (AdjoinRoot.mk _ g)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass (p : SpecialBase) :
    specialCoeff0 (specialBaseClass p) = p := by
  change
    (_root_.Polynomial.C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass (p : SpecialBase) :
    specialCoeffV (specialBaseClass p) = 0 := by
  change
    (_root_.Polynomial.C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_vClass :
    specialCoeff0 N13SpecialInfinityChart.vClass = 0 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_vClass :
    specialCoeffV N13SpecialInfinityChart.vClass = 1 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
    norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeff0
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = 0 := by
  change specialCoeff0
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = 0
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeffV
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = p := by
  change specialCoeffV
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = p
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reduction is coefficientwise in the rank-two bases. -/
@[simp] theorem reduce_integralCoeff0 (z : IntegralRing) :
    specialCoeff0 (reduceCoordinate z) =
      reducePoly (integralCoeff0 z) := by
  calc
    specialCoeff0 (reduceCoordinate z) =
        specialCoeff0
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeff0 z) := by
      simp
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralCoeffV (z : IntegralRing) :
    specialCoeffV (reduceCoordinate z) =
      reducePoly (integralCoeffV z) := by
  calc
    specialCoeffV (reduceCoordinate z) =
        specialCoeffV
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeffV z) := by
      simp
end
end MazurProof.N13IntegralInfinityReduction
end
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
abbrev plus := N13InfinityChartMarking.positiveIntegralExpansion
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
abbrev minus := N13InfinityChartMarking.negativeIntegralExpansion
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
abbrev r₀ := N13FormalInfinityBranches.branchZero
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
abbrev r₁ := N13FormalInfinityBranches.branchOne
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_base (p : R₂[X]) : plus (base p) = beta p := by
  simp [plus, base, N13InfinityChartMarking.positiveIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchZero]
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_base (p : R₂[X]) : minus (base p) = beta p := by
  simp [minus, base, N13InfinityChartMarking.negativeIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchOne]
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_v : plus N13IntegralInfinityChart.vClass = r₀ := by
  simp [plus, N13InfinityChartMarking.positiveIntegralExpansion]
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_v : minus N13IntegralInfinityChart.vClass = r₁ := by
  simp [minus, N13InfinityChartMarking.negativeIntegralExpansion]
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_normal_form (z : B) :
    plus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₀ := by
  calc
    plus z = plus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg plus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, plus_base, plus_base, plus_v]
end
end MazurProof.N13InfinityBranchJets
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
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_normal_form (z : B) :
    minus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₁ := by
  calc
    minus z = minus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg minus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, minus_base, minus_base, minus_v]
end
end MazurProof.N13InfinityBranchJets
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₀_constant : PowerSeries.constantCoeff r₀ = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.map PadicInt.toZMod
    N13FormalInfinityBranches.branchZero) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff, map_zero]
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
theorem r₁_constant : PowerSeries.constantCoeff r₁ = 1 := by
  rw [r₁_eq]
  norm_num [h, r₀_constant]
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
@[simp] theorem plus_t : plus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (plus_base X).trans (by simp [beta])
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
@[simp] theorem minus_t : minus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (minus_base X).trans (by simp [beta])
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem plus_normal_form (z : B) :
    plus z = beta (N13IntegralInfinityReduction.specialCoeff0 z) +
      beta (N13IntegralInfinityReduction.specialCoeffV z) * r₀ := by
  calc
    plus z = plus
        (N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeff0 z) +
          N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeffV z) *
            N13SpecialInfinityChart.vClass) :=
      congrArg plus (N13IntegralInfinityReduction.special_recompose z).symm
    _ = _ := by rw [map_add, map_mul, plus_base, plus_base, plus_v]
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem minus_normal_form (z : B) :
    minus z = beta (N13IntegralInfinityReduction.specialCoeff0 z) +
      beta (N13IntegralInfinityReduction.specialCoeffV z) * r₁ := by
  calc
    minus z = minus
        (N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeff0 z) +
          N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeffV z) *
            N13SpecialInfinityChart.vClass) :=
      congrArg minus (N13IntegralInfinityReduction.special_recompose z).symm
    _ = _ := by rw [map_add, map_mul, minus_base, minus_base, minus_v]
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
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
@[simp] theorem choose_zero : choose 0 = N13InfinityPointPicardRealization.infinityPlusData := by
  simp [choose]
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
@[simp] theorem divisorCode_mk
    (P Q : N13AbelFiberTwoModel.CurvePoint) :
    divisorCode s(P, Q) = pointCode P + pointCode Q := by
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
theorem pointCode_eq_codeBP (P : N13AbelFiberTwoModel.CurvePoint) :
    pointCode P = codeBP (curvePointEquiv P) := by
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
@[simp] theorem picCode_abel (D : EffectiveDivisorTwo) :
    picCode (abel D) = divisorCode D :=
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13.SpecialCuspCodeChecks
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction
/-- The sheet at x = 1 is reversed by the good-model coordinate change. -/
theorem pointCode_cusp (c : N13Mumford.Cusp13) :
    pointCode (specialCuspEquiv c) =
      match c with
      | .infinityPlus => 8
      | .infinityMinus => -8
      | .zeroPlus => 1
      | .zeroMinus => -1
      | .negOnePlus => -7
      | .negOneMinus => 7 := by
  rw [pointCode_eq_codeBP, curvePointEquiv_specialCuspEquiv]
  cases c <;> norm_num [codeBP, cuspCoordinate, baseAmplitude]
end
end MazurProof.N13.SpecialCuspCodeChecks
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13.SpecialCuspCodeChecks
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction
/-- The raw code of the doubled positive anchor is 16. -/
theorem divisorCode_double_anchor :
    divisorCode s(specialCuspEquiv .infinityPlus,
      specialCuspEquiv .infinityPlus) = 16 := by
  rw [divisorCode_mk, pointCode_cusp]
  norm_num
end
end MazurProof.N13.SpecialCuspCodeChecks
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
theorem chosen_zero_specialClass : (N13CalibratedChooser.choose 0).toSpecialPic =
    N13RationalPointEndgame.specialPointClass N13RationalPointEndgame.specialAnchor := by
  rw [N13CalibratedChooser.choose_zero, N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
/-- Pointwise compatibility with the actual proper reduction, recentered at
the same positive infinity anchor used by the rational Abel map. -/
theorem specialization_rationalAbel (P : N13RationalPointEndgame.RationalCurvePoint) :
    specialization (N13RationalPointEndgame.rationalAbel P) =
      pointCode (N13ProperCurveReduction.reduceCurve P) - pointCode N13RationalPointEndgame.specialAnchor := by
  change divisorCode (chosenDivisor (N13RationalPointEndgame.rationalAbel P)) -
      divisorCode (chosenDivisor 0) = _
  change picCode (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic -
      picCode (N13CalibratedChooser.choose 0).toSpecialPic = _
  rw [HuangN13.N13ConstructedSpecialization.chosen_point_specialClass, chosen_zero_specialClass]
  change divisorCode _ - divisorCode _ = _
  simp only [N13RationalPointEndgame.specialPointClass, picCode_abel, divisorCode_mk]
  ring
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem baseDivisor_code : divisorCode baseDivisor = 8 := by
  rw [baseDivisor, divisorCode_mk,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem baseDivisor_not_canonical :
    ¬ N13AbelFiberTwoModel.IsCanonical baseDivisor := by
  rintro ⟨b, hb⟩
  have hz : divisorCode baseDivisor = 0 := by
    rw [← hb, divisorCode_canonicalDivisor]
  rw [baseDivisor_code] at hz
  exact (by decide : (8 : ZMod 19) ≠ 0) hz
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem divisor_eq_base_of_code (D : EffectiveDivisorTwo)
    (h : divisorCode D = 8) : D = baseDivisor := by
  have he := (divisorCode_eq_iff_abelRel D baseDivisor).mp
    (h.trans baseDivisor_code.symm)
  rcases he with he | ⟨_, hb⟩
  · exact he
  · exact (baseDivisor_not_canonical hb).elim
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem chosen_zero_code : divisorCode (chosenDivisor 0) = 16 := by
  have h := congrArg picCode chosen_zero_specialClass
  change divisorCode (chosenDivisor 0) =
    divisorCode s(N13RationalPointEndgame.specialAnchor,
      N13RationalPointEndgame.specialAnchor) at h
  exact h.trans N13.SpecialCuspCodeChecks.divisorCode_double_anchor
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem specialization_cusp (c : N13Mumford.Cusp13) :
    specialization (N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint c)) =
      pointCode (specialCuspEquiv c) - 8 := by
  rw [specialization_rationalAbel, N13ProperCurveReduction.reduceCurve_cusp]
  change pointCode (specialCuspEquiv c) -
    pointCode (specialCuspEquiv .infinityPlus) = _
  rw [N13.SpecialCuspCodeChecks.pointCode_cusp .infinityPlus]
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem specialization_baseTranslate : specialization baseTranslate = 8 - 16 := by
  rw [baseTranslate, map_add, specialization_cusp, specialization_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem chosen_translated_code (z : Kernel) :
    divisorCode (chosenDivisor ((z : G) + baseTranslate)) = 8 := by
  have hz : specialization (z : G) = 0 := z.property
  have ht : specialization ((z : G) + baseTranslate) = 8 - 16 := by
    rw [map_add, hz, zero_add, specialization_baseTranslate]
  change divisorCode (chosenDivisor ((z : G) + baseTranslate)) -
    divisorCode (chosenDivisor 0) = 8 - 16 at ht
  rw [chosen_zero_code] at ht
  exact sub_left_injective ht
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
/-- The literal special divisor of the same chosen geometric witness. -/
theorem chosen_translated_divisor (z : Kernel) :
    (N13CalibratedChooser.choose ((z : G) + baseTranslate)).specialDivisor =
      baseDivisor :=
  divisor_eq_base_of_code _ (chosen_translated_code z)
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
private theorem constantCoeff_map_coe (p : Polynomial N13IntegralInfinityReduction.R₂) :
    PowerSeries.constantCoeff (PowerSeries.map N13IntegralInfinityReduction.reduceBase
      (p : PowerSeries N13IntegralInfinityReduction.R₂)) =
      N13IntegralInfinityReduction.reduceBase (p.coeff 0) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    Polynomial.coeff_coe]
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
theorem plus_constant_reduction (a : B) :
    PowerSeries.constantCoeff (N13SpecialInfinityBranchJets.plus (red a)) =
      redBase (PowerSeries.constantCoeff (positiveIntegralExpansion a)) := by
  rw [N13SpecialInfinityBranchJets.plus_normal_form,
    N13InfinityBranchJets.plus_normal_form]
  simp [N13SpecialInfinityBranchJets.beta_eq_coe,
    N13InfinityBranchJets.beta_eq_coe,
    N13SpecialInfinityBranchJets.r₀_constant,
    N13FormalInfinityBranches.branchZero_constantCoeff,
    N13IntegralInfinityReduction.reducePoly, constantCoeff_map_coe]
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
theorem minus_constant_reduction (a : B) :
    PowerSeries.constantCoeff (N13SpecialInfinityBranchJets.minus (red a)) =
      redBase (PowerSeries.constantCoeff (negativeIntegralExpansion a)) := by
  rw [N13SpecialInfinityBranchJets.minus_normal_form,
    N13InfinityBranchJets.minus_normal_form]
  simp [N13SpecialInfinityBranchJets.beta_eq_coe,
    N13InfinityBranchJets.beta_eq_coe,
    N13SpecialInfinityBranchJets.r₁_constant,
    N13FormalInfinityBranches.branchOne_constantCoeff,
    N13IntegralInfinityReduction.reducePoly, constantCoeff_map_coe,
    ZMod.neg_eq_self_mod_two]
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
theorem baseDivisor_infinity_t_sub_one_mem :
    N13SpecialInfinityChart.tClass - 1 ∈
      (N13SpecialDivisorCharts.ofDivisor baseDivisor).infinityIdeal := by
  change N13SpecialInfinityChart.tClass - 1 ∈
    (⊤ : Ideal S) * N13SpecialDivisorCharts.infinityPointIdeal 1 0
  rw [Ideal.top_mul]
  change N13SpecialInfinityChart.tClass - 1 ∈
    Ideal.span ({N13SpecialInfinityChart.tClass -
      algebraMap (Polynomial (ZMod 2)) S (Polynomial.C 1),
      N13SpecialInfinityChart.vClass -
        algebraMap (Polynomial (ZMod 2)) S (Polynomial.C 0)} : Set S)
  apply Ideal.subset_span
  simp
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13KernelInfinityMultiplicity.instFactPrimeOfNatNat_fLT
private theorem multiplicity_zero
    (I : Ideal B) (f : B →+* P) (g : S →+* SP)
    (hconstant : ∀ a, PowerSeries.constantCoeff (g (red a)) =
      redBase (PowerSeries.constantCoeff (f a)))
    (ht : g N13SpecialInfinityChart.tClass = PowerSeries.X)
    (hmem : N13SpecialInfinityChart.tClass - 1 ∈ Ideal.map red I)
    (n : ℕ)
    (hn : Ideal.map (N13TwoAdicInfinityCompatibility.powerMap.comp f) I =
      Ideal.span ({PowerSeries.X ^ n} : Set QP)) : n = 0 := by
  by_contra hpos
  let e : S →+* ZMod 2 := PowerSeries.constantCoeff.comp g
  have hI : Ideal.map red I ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change e (red a) = 0
    have hm := Ideal.mem_map_of_mem
      (N13TwoAdicInfinityCompatibility.powerMap.comp f) ha
    rw [hn, Ideal.mem_span_singleton] at hm
    have hc := PowerSeries.X_pow_dvd_iff.mp hm 0 (Nat.pos_of_ne_zero hpos)
    have hi : PowerSeries.constantCoeff (f a) = 0 := by
      apply N13TwoAdicInfinityCompatibility.coeffMap_injective
      simpa [N13TwoAdicInfinityCompatibility.powerMap,
        N13TwoAdicInfinityCompatibility.coeffMap] using hc
    change PowerSeries.constantCoeff (g (red a)) = 0
    rw [hconstant, hi, map_zero]
  have hz : e (N13SpecialInfinityChart.tClass - 1) = 0 := hI hmem
  have hv : e (N13SpecialInfinityChart.tClass - 1) = -1 := by
    simp [e, ht]
  rw [hv] at hz
  exact neg_ne_zero.mpr one_ne_zero hz
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem multiplicities_zero_of_special_divisor
    (D : Data) (hs : D.specialDivisor = baseDivisor)
    (p m : ℕ) (hm : HasInfinityMultiplicities D.charts p m) : p = 0 ∧ m = 0 := by
  have ht : N13SpecialInfinityChart.tClass - 1 ∈ Ideal.map red D.charts.infinityIdeal := by
    have h := D.special_infinity
    rw [hs] at h
    change Ideal.map red D.charts.infinityIdeal = _ at h
    rw [h]
    exact baseDivisor_infinity_t_sub_one_mem
  exact ⟨multiplicity_zero _ positiveIntegralExpansion N13SpecialInfinityBranchJets.plus
      plus_constant_reduction N13SpecialInfinityBranchJets.plus_t ht p hm.1,
    multiplicity_zero _ negativeIntegralExpansion N13SpecialInfinityBranchJets.minus
      minus_constant_reduction N13SpecialInfinityBranchJets.minus_t ht m hm.2⟩
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The same certified witness has affine degree two and effective nInf=-1.
Consequently its actual raw mark is -2 before balancing the graph. -/
theorem certified_finite_graph (D : Data) (hD : Certified D)
    (hs : D.specialDivisor = baseDivisor) :
    ∃ E : N13Mumford.SemiMumford Q₂,
      EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
      AffineVerticallySaturated D.charts := by
  obtain ⟨E, he, hr, hsat, hm⟩ := hD
  obtain ⟨hp, hn⟩ := multiplicities_zero_of_special_divisor D hs _ _ hm
  have hpc := positiveMultiplicity_cast E he
  have hnc := negativeMultiplicity_cast E he
  rw [hp] at hpc
  rw [hn] at hnc
  refine ⟨E, he, ?_, ?_, hr, hsat⟩ <;> omega
end
end MazurProof.N13KernelInfinityMultiplicity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelInfinityMultiplicity
noncomputable section
open N13KernelBaseDivisor N13InfinityChartMarking
open N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem chosen_translated_finite_graph (z : Kernel) :
    ∃ E : N13Mumford.SemiMumford Q₂,
      EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      genericRaw (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).charts
        (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
      AffineVerticallySaturated
        (N13CalibratedChooser.choose ((z : N13ConstructedSpecialization.G) +
          baseTranslate)).charts :=
  certified_finite_graph _ (HuangN13.N13CalibratedChooser.choose_certified _)
    (chosen_translated_divisor z)
end
end MazurProof.N13KernelInfinityMultiplicity
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution (z : MazurProof.N13KernelBaseDivisor.Kernel) :
    ∃ E : MazurProof.N13Mumford.SemiMumford MazurProof.N13TwoChartPicardRealization.Q₂,
      MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      MazurProof.N13TwoChartPicardRealization.genericRaw (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).charts
        (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated
        (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).charts := by
  exact MazurProof.N13KernelInfinityMultiplicity.chosen_translated_finite_graph z
