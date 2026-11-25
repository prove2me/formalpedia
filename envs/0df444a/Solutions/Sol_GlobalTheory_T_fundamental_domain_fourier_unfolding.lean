-- Prove2me | solution 1 for GlobalTheory.T.fundamental_domain_fourier_unfolding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:16.23887+00:00
-- url     : https://prove2.me/submissions/22ddcbda-96d9-456b-ae4b-525d303f3ea1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfoldingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_unfold_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A) (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y) (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam) (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1) (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ) (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X) (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q) (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e) (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b)) (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b), Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | exact GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | (intros; apply GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs <;> assumption)
end _root_.GlobalTheory.T
