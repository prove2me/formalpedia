-- Prove2me | solution 1 for GlobalTheory.T.affine_chart_ideal_prime_and_saturated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:04.70688+00:00
-- url     : https://prove2.me/submissions/0c63c099-e3b1-412c-a810-be0da4f6c4ba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_ideal_isPrime_and_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k), IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a → (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff <;> assumption)
end _root_.GlobalTheory.T
