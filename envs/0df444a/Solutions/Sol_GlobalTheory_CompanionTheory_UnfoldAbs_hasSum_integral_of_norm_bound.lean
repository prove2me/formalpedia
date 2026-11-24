-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnfoldAbs.hasSum_integral_of_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:30.893932+00:00
-- url     : https://prove2.me/submissions/b513a151-29e5-4e56-a690-f1a3c16a602d

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
theorem _root_.solution {A Z : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] [Countable Z] (G : Z → A → ℂ)
    (hm : ∀ q, AEStronglyMeasurable (G q) μ) (M : ℝ)
    (hb : ∀ b, Summable (fun q => ‖G q b‖) ∧ ∑' q, ‖G q b‖ ≤ M) :
    HasSum (fun q => ∫ b, G q b ∂μ) (∫ b, ∑' q, G q b ∂μ) := by
  have hbd : ∀ q b, ‖G q b‖ ≤ M := fun q b =>
    ((hb b).1.le_tsum q (fun _ _ => norm_nonneg _)).trans (hb b).2
  have hint : ∀ q, Integrable (G q) μ := fun q =>
    Integrable.of_bound (hm q) M (ae_of_all _ (hbd q))
  refine hasSum_integral_of_summable_integral_norm hint ?_
  refine summable_of_sum_le (c := ∫ _, M ∂μ)
    (fun q => integral_nonneg fun _ => norm_nonneg _) ?_
  intro s
  rw [← integral_finset_sum s (fun q _ => (hint q).norm)]
  exact integral_mono (integrable_finset_sum _ fun q _ => (hint q).norm) (integrable_const _)
    (fun b => ((hb b).1.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans (hb b).2)
end GlobalTheory.CompanionTheory.UnfoldAbs
