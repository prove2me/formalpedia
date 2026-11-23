-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneParamFourier.integrable_mul_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:07.532722+00:00
-- url     : https://prove2.me/submissions/5a4e7c7c-4e82-4b1a-8940-0882ea4ae392

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneParamFourier
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]
namespace GlobalTheory.CompanionTheory.OneParamFourier
theorem _root_.solution {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]
end GlobalTheory.CompanionTheory.OneParamFourier
