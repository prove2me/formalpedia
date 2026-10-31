-- Prove2me | solution 1 for HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:46:38.633803+00:00
-- url     : https://prove2.me/submissions/3aca8198-a9f4-4eec-a08e-2abfda6ea501

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_finite_sheet_difference
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_sheet_difference

set_option autoImplicit false

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
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem pointCode_eq_counts (P : CurvePoint) :
    N13SpecialAbelCode.pointCode P =
      (finitePointOrder 0 false P : ZMod 19) - finitePointOrder 0 true P +
        7 * (finitePointOrder 1 false P : ZMod 19) - 7 * finitePointOrder 1 true P +
        8 * (N13SpecialDivisorBranchOrders.pointOrder false P : ZMod 19) -
        8 * N13SpecialDivisorBranchOrders.pointOrder true P := by
  cases P with
  | inl P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.1 (ZMod.pow_card P.1.1) with hx | hx <;>
      rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.2 (ZMod.pow_card P.1.2) with hy | hy <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hx, hy]
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv <;>
      simp [N13SpecialAbelCode.pointCode, N13SpecialAbelCode.baseAmplitude,
        N13AbelFiberTwoModel.curvePointEquiv, finitePointOrder,
        N13SpecialDivisorBranchOrders.pointOrder, hv]
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
def countCode (D : EffectiveDivisorTwo) : ZMod 19 :=
  (finiteDivisorOrder 0 false D : ZMod 19) - finiteDivisorOrder 0 true D +
    7 * (finiteDivisorOrder 1 false D : ZMod 19) - 7 * finiteDivisorOrder 1 true D +
    8 * (N13SpecialDivisorBranchOrders.divisorOrder false D : ZMod 19) -
    8 * N13SpecialDivisorBranchOrders.divisorOrder true D
end
end MazurProof.N13SpecialFinitePointOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
theorem divisorCode_eq_counts (D : EffectiveDivisorTwo) : N13SpecialAbelCode.divisorCode D = countCode D := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [N13SpecialAbelCode.divisorCode_mk, pointCode_eq_counts, pointCode_eq_counts]
  simp only [countCode, finiteDivisorOrder_mk, N13SpecialDivisorBranchOrders.divisorOrder_mk, Nat.cast_add]
  ring
end
end MazurProof.N13SpecialFinitePointOrders
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
open N13SpecialDivisorBranchOrders
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem finite_sheet_difference
    (a : K) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (includeSeries (finiteBranch a false z)).order - (includeSeries (finiteBranch a true z)).order =
      ((finiteTensorOrder a false F H : ℤ) - finiteTensorOrder a true F H) -
        ((finiteTensorOrder a false D E : ℤ) - finiteTensorOrder a true D E) := by
  exact HuangN13.N13SpecialDegreeFourCode.finite_sheet_difference a D E F H h z hz hcross
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
open N13SpecialDivisorBranchOrders
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem infinity_sheet_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (plus z).order - (minus z).order =
      ((tensorOrder false F H : ℤ) - tensorOrder true F H) -
        ((tensorOrder false D E : ℤ) - tensorOrder true D E) := by
  exact HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference D E F H h z hz hcross
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
open N13SpecialDivisorBranchOrders
open N13SpecialFiniteBranchFaithfulness hiding R
open N13SpecialFinitePointOrders N13SpecialSixJetOrders
theorem weightedLocalCode_eq_code_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    weightedLocalCode z =
      (N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H) -
        (N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E) := by
  have hzero := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 0 D E F H h z hz hcross)
  have hone := congrArg (fun n : ℤ => (n : ZMod 19)) (finite_sheet_difference 1 D E F H h z hz hcross)
  have hinfinity := congrArg (fun n : ℤ => (n : ZMod 19)) (infinity_sheet_difference D E F H h z hz hcross)
  push_cast at hzero hone hinfinity
  rw [divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts, divisorCode_eq_counts]
  change ((includeSeries (finiteBranch 0 false z)).order : ZMod 19) -
      ((includeSeries (finiteBranch 0 true z)).order : ZMod 19) +
      7 * ((includeSeries (finiteBranch 1 false z)).order : ZMod 19) -
      7 * ((includeSeries (finiteBranch 1 true z)).order : ZMod 19) +
      8 * ((plus z).order : ZMod 19) - 8 * ((minus z).order : ZMod 19) = _
  simp only [countCode, finiteTensorOrder, tensorOrder, Nat.cast_add] at hzero hone hinfinity ⊢
  linear_combination hzero + 7 * hone + 8 * hinfinity
end
end MazurProof.N13SpecialDegreeFourCode
end
end

open Polynomial
theorem solution
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    MazurProof.N13SpecialSixJetOrders.weightedLocalCode z =
      (MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H) -
        (MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E) := by
  exact MazurProof.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference D E F H h z hz hcross
