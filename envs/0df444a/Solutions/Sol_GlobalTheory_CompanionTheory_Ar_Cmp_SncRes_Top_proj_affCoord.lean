-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.proj_affCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:52.283527+00:00
-- url     : https://prove2.me/submissions/3fa315cd-5a53-4448-84af-5fe4d405a57a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_proj_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
theorem _root_.solution (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    proj (affCoord p (rep x)) = x.1 := by
  have hA : affCoord p (rep x) = fun q => (rep x ⟨q.1, p q.1⟩)⁻¹ * rep x q := by
    funext q; simp [affCoord, div_eq_inv_mul]
  rw [hA, proj_smul (fun k => (rep x ⟨k, p k⟩)⁻¹) (fun k => inv_ne_zero (hx k)), proj_rep]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
