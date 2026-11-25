-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:32:25.825789+00:00
-- url     : https://prove2.me/submissions/f4191445-f789-458b-91cc-32e5c6f366cf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomial
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_coord_image
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_coord_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) :=
  ⟨coord_image hP, fun p p' x hx => coord_trans p p' x hx⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
