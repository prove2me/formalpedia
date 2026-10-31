-- Prove2me | solution 1 for HuangN13.N13ConstructedSpecialization.divisorCode_eq_of_comparison
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:31:48.691027+00:00
-- url     : https://prove2.me/submissions/f1e56c2f-43c5-447c-8f39-13f2b2425007

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_ComparisonOrdersCore
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_degreeFourCode_eq_of_comparison

set_option autoImplicit false

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
/-- The exact previously missing B03 bridge, without new hypotheses. -/
theorem degreeFourCode_eq_of_comparison
    (D E F H : N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor D) (N13SpecialDivisorCharts.ofDivisor E))
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor F) (N13SpecialDivisorCharts.ofDivisor H))) :
    N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E =
      N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H := by
  exact HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison D E F H h
end
end MazurProof.N13SpecialDegreeFourCode
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
def tensor_comparison_right
    (L M U : N13TwoChartSpecialRestriction.ChartPair) (h : SpecialComparison L M) :
    SpecialComparison (tensor L U) (tensor M U) where
  aNum := h.aNum
  aDen := h.aDen
  iNum := h.iNum
  iDen := h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := by
    change Ideal.span ({h.aNum} : Set As) * (L.affineIdeal * U.affineIdeal) =
      Ideal.span ({h.aDen} : Set As) * (M.affineIdeal * U.affineIdeal)
    rw [← mul_assoc, h.affine_eq, mul_assoc]
  infinity_eq := by
    change Ideal.span ({h.iNum} : Set Bs) * (L.infinityIdeal * U.infinityIdeal) =
      Ideal.span ({h.iDen} : Set Bs) * (M.infinityIdeal * U.infinityIdeal)
    rw [← mul_assoc, h.infinity_eq, mul_assoc]
  overlap_eq := h.overlap_eq
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
theorem divisorCode_eq_of_comparison (D E : EffectiveDivisorTwo)
    (h : SpecialComparison (ofDivisor D) (ofDivisor E)) : divisorCode D = divisorCode E := by
  have he := degreeFourCode_eq_of_comparison D D E D
    (tensor_comparison_right _ _ (ofDivisor D) h)
  exact add_right_cancel he
end
end MazurProof.N13ConstructedSpecialization
end
end

open Polynomial
theorem solution (D E : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) : MazurProof.N13SpecialAbelCode.divisorCode D = MazurProof.N13SpecialAbelCode.divisorCode E := by
  exact MazurProof.N13ConstructedSpecialization.divisorCode_eq_of_comparison D E h
