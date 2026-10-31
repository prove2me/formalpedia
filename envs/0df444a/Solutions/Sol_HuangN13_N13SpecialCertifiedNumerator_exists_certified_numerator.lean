-- Prove2me | solution 1 for HuangN13.N13SpecialCertifiedNumerator.exists_certified_numerator
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:46:35.554009+00:00
-- url     : https://prove2.me/submissions/392e8ef9-36d2-46d4-bbf4-0c0861f8a8d2

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SpecialJetCodeCore
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_supported_small_function_certificate
import Theorems.Thm_HuangN13_N13SpecialSmallNumerator_exists_small_supported_numerator
import Theorems.Thm_MazurProof_N13SpecialCertifiedNumerator_dvd_fixed_support

set_option autoImplicit false

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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
/-- Reduction to the genuine 32-by-4 polynomial search space over F2.
The small numerator retains the input fraction and has supported norm. -/
theorem exists_small_supported_numerator
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ p q : K[X], ∃ i j : ℕ,
      p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 ∧ i + j ≤ 16 ∧
      N13SpecialAffineNorm.linear p q ≠ 0 ∧
      h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) =
        h.aDen * N13SpecialAffineNorm.linear p q ∧
      N13SpecialAffineNorm.normPolynomial p q ≠ 0 ∧
      N13SpecialAffineNorm.normPolynomial p q ∣ X ^ i * (X - 1) ^ j := by
  exact HuangN13.N13SpecialSmallNumerator.exists_small_supported_numerator D E F H h
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
/-- The norm-support restriction leaves only genuine nonzero nine-jets,
and every surviving pair has zero weighted code. The common infinity
shift -4 cancels between the last two coefficients, whose weights sum to 0. -/
theorem supported_small_function_certificate :
    ∀ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
          (X : K[X]) ^ 16 * (X - 1) ^ 16 →
        (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
          (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
          ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
        weightedJetCode a b = 0 := by
  exact HuangN13.N13SpecialSmallFunctionCertificate.supported_small_function_certificate
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialCertifiedNumerator
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair
theorem numerator_coefficients (p : K[X]) (hp : p.natDegree ≤ 4) :
    numerator (fun i : Fin 5 => p.coeff i) = p := by
  unfold numerator
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) 5]
  simpa only [C_mul_X_pow_eq_monomial] using (p.as_sum_range' 5 (by omega)).symm
end
end MazurProof.N13SpecialCertifiedNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialCertifiedNumerator
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair
theorem ordinate_coefficients (q : K[X]) (hq : q.natDegree ≤ 1) :
    ordinate (fun i : Fin 2 => q.coeff i) = q := by
  have hh := (q.as_sum_range' 2 (by omega)).symm
  simpa [ordinate, Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial] using hh
end
end MazurProof.N13SpecialCertifiedNumerator
end
end

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
  obtain ⟨p, q, i, j, hp, hq, hij, hn, hcross, _, hnorm⟩ :=
    N13SpecialSmallNumerator.exists_small_supported_numerator D E F H h
  let a : Fin 5 → K := fun i => p.coeff i
  let b : Fin 2 → K := fun i => q.coeff i
  have ha : numerator a = p := numerator_coefficients p hp
  have hb : ordinate b = q := ordinate_coefficients q hq
  have hs : N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
      (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
    rw [ha, hb]
    exact dvd_fixed_support _ i j hij hnorm
  obtain ⟨hjets, hcode⟩ := supported_small_function_certificate a b hs
  exact ⟨a, b, by rwa [ha, hb], by rwa [ha, hb], hjets, hcode⟩
end
end MazurProof.N13SpecialCertifiedNumerator
end
end

open Polynomial
theorem solution
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    ∃ (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K),
      MazurProof.N13SpecialAffineNorm.linear (MazurProof.N13SpecialSmallFunctionCertificate.numerator a) (MazurProof.N13SpecialSmallFunctionCertificate.ordinate b) ≠ 0 ∧
      h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) =
        h.aDen * MazurProof.N13SpecialAffineNorm.linear (MazurProof.N13SpecialSmallFunctionCertificate.numerator a) (MazurProof.N13SpecialSmallFunctionCertificate.ordinate b) ∧
      (∀ i : Fin 6, MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i < 9 ∧
        (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff (MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i) ≠ 0 ∧
        ∀ j : Fin 9, (j : ℕ) < MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i → (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff j = 0) ∧
      MazurProof.N13SpecialSmallFunctionCertificate.weightedJetCode a b = 0 := by
  exact MazurProof.N13SpecialCertifiedNumerator.exists_certified_numerator D E F H h
