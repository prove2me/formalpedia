-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnfoldAbs.integrable_of_lattice_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:31.944953+00:00
-- url     : https://prove2.me/submissions/b3268947-e32d-4c9d-ba5e-bc07125ce8bb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnfoldAbs
namespace GlobalTheory.CompanionTheory.UnfoldAbs
theorem _root_.solution {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (F0 : A → ℂ) (hm : AEStronglyMeasurable F0 lam) (M : ℝ)
    (hb : ∀ b, Summable (fun l : Λ => ‖F0 ((l : A) + b)‖) ∧ ∑' l : Λ, ‖F0 ((l : A) + b)‖ ≤ M) :
    Integrable F0 lam := by
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have e : ∫⁻ b, ‖F0 b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 ((l : A) + b)‖ₑ ∂lam :=
    h𝓖.lintegral_eq_tsum'' _
  have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 ((l : A) + b)‖ₑ) (lam.restrict 𝓖) := fun l =>
    ((hm.comp_measurePreserving (measurePreserving_add_left lam (l : A))).enorm).restrict
  rw [e, ← lintegral_tsum hmeas]
  calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 ((l : A) + b)‖ₑ ∂lam
      ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal M ∂lam := by
        refine lintegral_mono (fun b => ?_)
        simp_rw [← ofReal_norm_eq_enorm]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb b).1]
        exact ENNReal.ofReal_le_ofReal (hb b).2
    _ < ⊤ := by simp [h1]
end GlobalTheory.CompanionTheory.UnfoldAbs
