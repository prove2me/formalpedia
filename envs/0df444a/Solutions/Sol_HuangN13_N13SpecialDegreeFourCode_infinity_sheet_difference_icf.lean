-- Prove2me | solution 1 for HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference_icf
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:39:06.894724+00:00
-- url     : https://prove2.me/submissions/e11724ea-291f-4602-8afb-a86d4874cbe9

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_cleared_order_balance

set_option autoImplicit false

namespace MazurProof.N13SpecialSmallNumerator
end MazurProof.N13SpecialSmallNumerator
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
theorem infinity_sheet_difference
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (plus z).order - (minus z).order =
      ((tensorOrder false F H : ℤ) - tensorOrder true F H) -
        ((tensorOrder false D E : ℤ) - tensorOrder true D E) := by
  have hp := HuangN13.N13SpecialDegreeFourCode.infinity_cleared_order_balance false D E F H h z hz hcross
  have hm := HuangN13.N13SpecialDegreeFourCode.infinity_cleared_order_balance true D E F H h z hz hcross
  change (plus z).order + _ + _ = _ at hp
  change (minus z).order + _ + _ = _ at hm
  omega
end
end MazurProof.N13SpecialDegreeFourCode
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialLaurentBranches.plus z).order - (MazurProof.N13SpecialLaurentBranches.minus z).order =
      ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false F H : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true F H) -
        ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false D E : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true D E) := by
  exact MazurProof.N13SpecialDegreeFourCode.infinity_sheet_difference D E F H h z hz hcross
