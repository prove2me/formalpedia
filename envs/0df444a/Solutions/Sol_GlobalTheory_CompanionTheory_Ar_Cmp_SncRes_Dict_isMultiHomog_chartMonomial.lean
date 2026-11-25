-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.isMultiHomog_chartMonomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:03:13.81194+00:00
-- url     : https://prove2.me/submissions/b8af369a-39af-4d6f-b89f-4e12003a382c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_C
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_X
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
theorem _root_.solution (p : (k : K) → ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k)
      (∑ k ∈ s, e k • (Pi.single k 1 : K → ℕ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (K := K) (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, p k⟩) (e k)) ih
  have h2 : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h3 := h Finset.univ
  rwa [h2] at h3
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
