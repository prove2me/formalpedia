-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.affCoord_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:11.497464+00:00
-- url     : https://prove2.me/submissions/12ec33da-ae1c-49f5-b644-d2bb368bc9ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_normSq_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_proj_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem


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
theorem _root_.solution (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    affCoord p (rep x) q = x.1 ⟨q.1, (q.2, p q.1)⟩ / x.1 ⟨q.1, (p q.1, p q.1)⟩ := by
  obtain ⟨k, i⟩ := q
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  have h1 : rep x ⟨k, p k⟩ ≠ 0 := hx k
  have h2 : starRingEnd ℂ (rep x ⟨k, p k⟩) ≠ 0 := by simpa using h1
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ h, mul_div_mul_right _ _ h2]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
