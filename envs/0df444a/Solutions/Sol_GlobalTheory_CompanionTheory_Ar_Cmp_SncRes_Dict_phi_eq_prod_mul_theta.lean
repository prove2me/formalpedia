-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.phi_eq_prod_mul_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:02.062448+00:00
-- url     : https://prove2.me/submissions/2f0cb8bf-c1c4-4530-82f1-172cfe694c7f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_eval__smul_d751c1e96760
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_zero_iff
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4

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
    phi Q f = (∏ k, phi Q (X ⟨k, p k⟩) ^ a k) * theta Q p f := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have h := eval₂_smul ((phi Q).comp C) (fun k => phi Q (X ⟨k, p k⟩))
    (fun q => phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩)) hf
  have h2 : (fun q : Σ k, ι k => phi Q (X ⟨q.1, p q.1⟩) * (phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩))) =
      fun q => phi Q (X q) := by
    funext q
    exact mul_div_cancel₀ _ (hx q.1)
  rw [h2, ← phi_eq_eval₂] at h
  exact h
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
