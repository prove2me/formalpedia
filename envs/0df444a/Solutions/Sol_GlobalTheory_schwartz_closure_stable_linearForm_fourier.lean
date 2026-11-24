-- Prove2me | solution 1 for GlobalTheory.schwartz_closure_stable_linearForm_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:29.471867+00:00
-- url     : https://prove2.me/submissions/5a1727b1-619e-4e40-811d-cb4f2a12e8bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourier
import Theorems.Thm_GlobalTheory_topologicalClosure_stable_of_continuousLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this
end GlobalTheory
