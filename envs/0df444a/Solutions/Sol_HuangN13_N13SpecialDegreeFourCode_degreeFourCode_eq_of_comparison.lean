-- Prove2me | solution 1 for HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:10:19.359072+00:00
-- url     : https://prove2.me/submissions/97b07dcf-e2f9-4ee1-ba77-5d0b3486510f

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore
import Definitions.Def_HuangN13_SpecialJetCodeCore
import Theorems.Thm_HuangN13_N13SpecialCertifiedNumerator_exists_certified_numerator
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_weightedLocalCode_eq_code_difference
import Theorems.Thm_HuangN13_N13SpecialSixJetOrders_weightedLocalCode_of_certified_jets

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialCertifiedNumerator
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair
theorem exists_certified_numerator
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.linear (numerator a) (ordinate b) ≠ 0 ∧
      h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) =
        h.aDen * N13SpecialAffineNorm.linear (numerator a) (ordinate b) ∧
      (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
        (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
        ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
      weightedJetCode a b = 0 := by
  exact HuangN13.N13SpecialCertifiedNumerator.exists_certified_numerator D E F H h
end
end MazurProof.N13SpecialCertifiedNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
theorem weightedLocalCode_of_certified_jets (a : Fin 5 → K) (b : Fin 2 → K)
    (hn : function a b ≠ 0)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (hcode : weightedJetCode a b = 0) : weightedLocalCode (function a b) = 0 := by
  exact HuangN13.N13SpecialSixJetOrders.weightedLocalCode_of_certified_jets a b hn hjets hcode
end
end MazurProof.N13SpecialSixJetOrders
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
  exact HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference D E F H h z hz hcross
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
/-- The exact previously missing B03 bridge, without new hypotheses. -/
theorem degreeFourCode_eq_of_comparison
    (D E F H : N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor D) (N13SpecialDivisorCharts.ofDivisor E))
      (N13SpecialDivisorCharts.tensor (N13SpecialDivisorCharts.ofDivisor F) (N13SpecialDivisorCharts.ofDivisor H))) :
    N13SpecialAbelCode.divisorCode D + N13SpecialAbelCode.divisorCode E =
      N13SpecialAbelCode.divisorCode F + N13SpecialAbelCode.divisorCode H := by
  obtain ⟨a, b, hn, hcross, hjets, hcode⟩ := N13SpecialCertifiedNumerator.exists_certified_numerator D E F H h
  have hz := weightedLocalCode_of_certified_jets a b hn hjets hcode
  have he := weightedLocalCode_eq_code_difference D E F H h (function a b) hn hcross
  rw [hz] at he
  exact (sub_eq_zero.mp he.symm).symm
end
end MazurProof.N13SpecialDegreeFourCode
end
end

open Polynomial
theorem solution
    (D E F H : MazurProof.N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E))
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E =
      MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H := by
  exact MazurProof.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison D E F H h
