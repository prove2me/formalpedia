-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.theta_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:02.3258+00:00
-- url     : https://prove2.me/submissions/ae1c81d0-df3d-4dd6-8496-4e8681612500

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_prod_mul_theta

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
theorem _root_.solution (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    theta Q p f = 0 ↔ f ∈ Q := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hprod : (∏ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hx k)
  rw [← phi_eq_zero_iff Q f, phi_eq_prod_mul_theta Q p hp hf]
  simp [hprod]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
