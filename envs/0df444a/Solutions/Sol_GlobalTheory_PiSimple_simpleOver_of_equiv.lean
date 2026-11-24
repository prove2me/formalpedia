-- Prove2me | solution 1 for GlobalTheory.PiSimple.simpleOver_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:54.208033+00:00
-- url     : https://prove2.me/submissions/dc41830c-20cf-48f6-a661-f9c8a33219d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (e : V ≃ₗ[ℂ] W) (G : Set (Module.End ℂ V)) (G' : Set (Module.End ℂ W))
    (K : Submodule ℂ V) (K' : Submodule ℂ W) (hK : K.map (e : V →ₗ[ℂ] W) = K')
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ x, g' (e x) = e (g x)) (h : SimpleOver G' K') :
    SimpleOver G K := by
  intro N hN hKN
  have hs : Stab G' (N.map (e : V →ₗ[ℂ] W)) := by
    rintro g' hg' _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hc⟩ := hG g' hg'
    exact ⟨g x, hN g hg x hx, by simpa using (hc x).symm⟩
  have hle : K' ≤ N.map (e : V →ₗ[ℂ] W) := hK ▸ Submodule.map_mono hKN
  have key : ∀ P : Submodule ℂ V, (P.map (e : V →ₗ[ℂ] W)).comap (e : V →ₗ[ℂ] W) = P := by
    intro P; ext x; simp
  rcases h _ hs hle with h1 | h1
  · left
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [← hK, key, key] at this
  · right
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [key, Submodule.comap_top] at this
end GlobalTheory.PiSimple
