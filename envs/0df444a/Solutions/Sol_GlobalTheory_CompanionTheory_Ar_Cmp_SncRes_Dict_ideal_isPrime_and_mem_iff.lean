-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:57:28.955051+00:00
-- url     : https://prove2.me/submissions/1a90988f-dbad-4eed-96bd-55e29a6e2a6b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_eq_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_ker_theta
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_map_renR_iff


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
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
      (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
        (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
  intro hQ hprime hp
  have hker := ker_theta Q hQ p hp
  refine ⟨?_, fun f a hf => ?_⟩
  · have h1 : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (theta Q p)
    exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
  · rw [SncRes.ideal, mem_map_renR_iff, ← hker, RingHom.mem_ker, theta_symm_bind₁ Q p hp,
      theta_eq_zero_iff Q p hp hf]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
