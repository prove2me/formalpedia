-- Prove2me | solution 1 for GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:53.564791+00:00
-- url     : https://prove2.me/submissions/0b291007-6651-40da-abdc-bc6d2a7d4151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourier
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourierStatement
import Theorems.Thm_GlobalTheory_schwartz_closure_stable_linearForm_fourier


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  first | exact @GlobalTheory.schwartz_closure_stable_linearForm_fourier | exact GlobalTheory.schwartz_closure_stable_linearForm_fourier | (intros; apply GlobalTheory.schwartz_closure_stable_linearForm_fourier <;> assumption)
end _root_.GlobalTheory.T
