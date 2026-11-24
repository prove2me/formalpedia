-- Prove2me | solution 1 for GlobalTheory.BadShare.trace_compLeft_funLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:16.772531+00:00
-- url     : https://prove2.me/submissions/7229f9cf-1d75-4225-a45d-1578c4edc092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
noncomputable section
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {G W : Type} [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : W →ₗ[ℂ] W) (f : G → G) :
    LinearMap.trace ℂ (G → W) (A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f) =
      ∑ x, if f x = x then LinearMap.trace ℂ W A else 0 := by
  have h : A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f =
      ∑ x, LinearMap.single ℂ (fun _ : G => W) x ∘ₗ (A ∘ₗ LinearMap.proj (f x)) := by
    refine LinearMap.ext fun φ => funext fun y => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, LinearMap.funLeft_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.trace_comp_comm']
  split_ifs with hx
  · congr 1
    ext w
    simp [hx]
  · have : (A ∘ₗ LinearMap.proj (f x)) ∘ₗ LinearMap.single ℂ (fun _ : G => W) x = 0 := by
      ext w
      simp [hx]
    rw [this, map_zero]
end GlobalTheory.BadShare
