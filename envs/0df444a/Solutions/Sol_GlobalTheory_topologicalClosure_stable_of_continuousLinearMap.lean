-- Prove2me | solution 1 for GlobalTheory.topologicalClosure_stable_of_continuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:00.617192+00:00
-- url     : https://prove2.me/submissions/22d38259-a29a-4ebe-af09-559632fecce9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourier

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
theorem _root_.solution {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)
end GlobalTheory
